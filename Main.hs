{- |
************************************************************************
*                                                                      *
*              A Linux VM emulator
*                                                                      *
************************************************************************

Synopsis:
$ strace -f -k -e trace=memory,process -o strace.data ls
$ prog strace.data --output=frame.data --trace=trace.data
$ Rscript mmap.R frame.data trace.data

The sections are:
1. Strace parser objects
2. Strace output parser
3. Pretty printers
4. Linux VM emulator
5. Utilities
6. Testing and debugging
7. IO

Note: all the functions are in underscore_case to distinguish them from
      the library functions (also because I like kernel code).

Bug: if a child pid has been recycled during the process's liftime,
     the behavior is undefined.

-}

module Main    where

import Numeric
import Pretty
import Invariant
import Hyper
import Sheaf
import PrettySheaf


import Data.Maybe
import Data.List
import Data.List.Split
import Data.Char
import Data.Hashable
import Data.Bits

import Data.Map (Map,(!))
import qualified Data.Map as Map

import Control.Exception

import Text.Printf
import Text.Regex.PCRE

import System.Environment
import System.Exit
import System.IO.Unsafe


{-
************************************************************************
*                                                                      *
*              1. Strace parser objects
*                                                                      *
************************************************************************
-}


data Strace = Strace
              { strace_tid     :: Integer
              , strace_syscall :: String
              , strace_args    :: SyscallArgs
              , strace_ret     :: SyscallRet
              , strace_stack   :: [StraceLine]
              } deriving (Eq,Show)

type SyscallArgs = [String]
type SyscallRet  = String

data StraceLine =
            Syscall
            { sl_tid     :: Integer
            , sl_syscall :: String
            , sl_args    :: SyscallArgs
            , sl_ret     :: SyscallRet
            }
          | SyscallError
            { sl_tid     :: Integer
            , sl_syscall :: String
            , sl_args    :: SyscallArgs
            , sl_ret     :: SyscallRet
            , sl_err     :: String
            }
          | SyscallUnfinished
            { sl_tid     :: Integer
            , sl_syscall :: String
            , sl_args    :: SyscallArgs
            }
          | SyscallResumed
            { sl_tid       :: Integer
            , sl_syscall   :: String
            , sl_args_rest :: SyscallArgs
            , sl_ret       :: SyscallRet
            }
          | SyscallResumedError
            { sl_tid       :: Integer
            , sl_syscall   :: String
            , sl_args_rest :: SyscallArgs
            , sl_ret       :: SyscallRet
            , sl_err       :: String
            }
          | StackTrace
            { sl_call_stack  :: String
            }
          | Exit
            { sl_tid    :: Integer
            , sl_status :: Integer
            }
          | Signal
            { sl_tid    :: Integer
            , sl_signal :: String
            , sl_args   :: SyscallArgs
            }
          deriving (Eq,Show)


type Id           = Int
type UniqueStrace = (Id, Strace)


{-
************************************************************************
*                                                                      *
*              2. Strace output parser
*                                                                      *
************************************************************************

   Run strace as:
   # strace -f -k -e trace=memory,process command
   You may need to compile strace, as '-k' is documented as an experimental feature

   @tbd: Just realized context-freeness is really necessary..
   @tbd: parse '-t', '-tt', etc.
-}

-- 18232 mmap(NULL, 8192, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = 0x7f3927f2a000
parse_syscall_entry :: String -> Maybe (String, String, String, String)
parse_syscall_entry x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^)]*)\\) *= *([\\S]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args, ret]] -> Just (tid, syscall, args, ret)
                otherwise                      -> Nothing

-- 18233 mlockall(MCL_CURRENT)             = -1 ENOMEM (Cannot allocate memory)
parse_syscall_entry_error :: String -> Maybe (String, String, String, String, String)
parse_syscall_entry_error x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^)]*)\\) *= *([\\S]+) +(\\w.*)$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args, ret, err]] -> Just (tid, syscall, args, ret, err)
                otherwise                           -> Nothing


-- 18253 mmap(0x7f390ac62000, 12288, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS, -1, 0 <unfinished ...>
parse_syscall_unfinished :: String -> Maybe (String, String, String)
parse_syscall_unfinished x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^<]*) *< *unfinished *\\.\\.\\.> *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args]] -> Just (tid, syscall, args)
                otherwise                 -> Nothing

-- 18253 <... mmap resumed> )              = 0x7f390ac62000
parse_syscall_resumed :: String -> Maybe (String, String, String, String)
parse_syscall_resumed x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *(.*) *\\) *= *([^()=\\s]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, arg_rest, ret]] -> Just (tid, syscall, arg_rest, ret)
                otherwise                          -> Nothing

-- 18253 <... mmap resumed> )              = -1 ENOMEM.*
parse_syscall_resumed_error :: String -> Maybe (String, String, String, String, String)
parse_syscall_resumed_error x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *(.*) *\\) *= *([^=\\s]+) +([^=]+)$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args_rest, ret, err]] -> Just (tid, syscall, args_rest, ret, err)
                otherwise                                -> Nothing


--  > /lib/x86_64-linux-gnu/ld-2.19.so(realloc+0x3dc) [0x1814c]
parse_stack_trace :: String -> Maybe String
parse_stack_trace x =
        let matches = x  =~ "^ *> *(.*) *$" :: [[String]]
        in
                case matches of
                [[_, trace]] -> Just trace
                otherwise    -> Nothing

-- 18232 +++ exited with 130 +++
parse_exit :: String -> Maybe (String, String)
parse_exit x = let matches = x  =~ "^ *(\\d+) +\\+\\+\\+ *exited +with +(\\d+) +\\+\\+\\+ *$" :: [[String]]
               in
                       case matches of
                       [[_, tid, status]] -> Just (tid, status)
                       otherwise          -> Nothing

-- 18239 --- SIGSEGV {si_signo=SIGSEGV, si_code=SEGV_ACCERR, si_addr=0x7f3927f28b80} ---
parse_signal :: String -> Maybe (String, String, String)
parse_signal x = let matches = x  =~ "^ *(\\d+) *--- *(\\w+) *{(.*)} *--- *$" :: [[String]]
               in
                       case matches of
                       [[_, tid, sig, args]] -> Just (tid, sig, args)
                       otherwise        -> Nothing


parse_line :: String -> StraceLine
parse_line s = case catMaybes
               [ fmap syscall_entry         $ parse_syscall_entry s,
                 fmap syscall_entry_error   $ parse_syscall_entry_error s,
                 fmap syscall_unfinished    $ parse_syscall_unfinished s,
                 fmap syscall_resumed       $ parse_syscall_resumed s,
                 fmap syscall_resumed_error $ parse_syscall_resumed_error s,
                 fmap stack_trace           $ parse_stack_trace s,
                 fmap exit                  $ parse_exit s,
                 fmap signal                $ parse_signal s
               ]
               of
                       [x]     -> x
                       []      -> error $ "cannot parse:" ++ s
                       (_:_:_) -> error $ "duplicate parse:" ++ s
        where
                syscall_entry       (tid, syscall, args, ret)
                        = Syscall (i tid) syscall (split args) ret
                syscall_entry_error (tid, syscall, args, ret, err)
                        = SyscallError (i tid) syscall (split args) ret err
                syscall_unfinished  (tid, syscall, args)
                        = SyscallUnfinished (i tid) syscall (split args)
                syscall_resumed     (tid, syscall, args_rest, ret)
                        = SyscallResumed (i tid) syscall (split args_rest) ret
                syscall_resumed_error (tid, syscall, args_rest, ret, err)
                        = SyscallResumedError (i tid) syscall (split args_rest) ret err
                stack_trace (trace)
                        = StackTrace trace
                exit (tid, status)
                        = Exit (i tid) (i status)
                signal (tid, signal, args)
                        = Signal (i tid) signal (split args)
                i = read
                split = map chomp . splitOn ","


-- |Parse whole strace output string
parse :: String -> [StraceLine]
parse s = map parse_line (lines s)

-- |Id is used to identify stack straces
strace_with_id :: [StraceLine] -> [(Id,Strace)]
strace_with_id = zip [1..] . strace

-- |Construct a syscall history from the stream strace lines
strace :: [StraceLine] -> [Strace]
strace (Syscall tid syscall args ret: rest) =
        let (traces, rest') = trace_lines rest
        in  (Strace tid syscall args ret traces) : strace rest'

strace (SyscallError tid syscall args ret err: rest) =
        let (traces, rest') = trace_lines rest
            -- Just skip errors atm
        in  strace rest'

strace (SyscallUnfinished tid syscall args: rest) =
        case search_resumed tid syscall rest
        of
                (SyscallResumed tid' syscall' args_rest ret', traces, rest') ->
                        if tid == tid' && syscall == syscall'
                        then
                                (Strace tid syscall (args ++ args_rest) ret' traces) : strace rest'
                        else
                                error $ "strace unfinished:" ++ show tid ++ show syscall
                -- skip errors
                (SyscallResumedError tid' syscall' args_rest ret' err, traces, rest') ->
                        if tid == tid' && syscall == syscall'
                        then
                                strace rest'
                        else
                                error $ "strace unfinished:" ++ show tid ++ show syscall

                _ ->            error $ "strace unfinished:" ++ show tid ++ show syscall

strace (SyscallResumed tid syscall args_rest ret: rest) =
        error $ "resumed without unfinished:" ++ show tid ++ syscall
strace (SyscallResumedError tid syscall args_rest ret err: rest) =
        error $ "resumed without unfinished:" ++ show tid ++ syscall
strace (StackTrace call_stack: rest)               =
        error $ "trace without syscall line:"
        ++ show call_stack ++ (render $ pp_list $ map pp_strace_line $ take 30 rest)

strace (Exit   tid status: rest)      =
        let (traces, rest') = trace_lines rest
        in  (Strace tid "exit" [] (show status) traces) : strace rest'

strace (Signal tid signal args: rest) =
        strace rest

strace [] = []


trace_lines :: [StraceLine] -> ([StraceLine], [StraceLine])
trace_lines = span is_stack_trace
        where
                is_stack_trace (StackTrace _) = True
                is_stack_trace _              = False

search_resumed :: Integer -> String -> [StraceLine] -> (StraceLine, [StraceLine], [StraceLine])
search_resumed tid syscall ls =
        let  (xs, (r:ys))   = break (is_resumed tid syscall) ls
             (traces, rest) = trace_lines ys
        in
                (r, traces, xs ++ rest)
        where
                is_resumed tid syscall (SyscallResumed tid' syscall' args_rest' ret') =
                        tid == tid' && syscall == syscall'
                is_resumed tid syscall (SyscallResumedError tid' syscall' args_rest' ret' err') =
                        tid == tid' && syscall == syscall'
                is_resumed tid syscall _ = False

dump_lines :: FilePath -> FilePath -> IO ()
dump_lines i o = readFile i >>=
                 return . parse >>=
                 return . render . pp_list . map pp_strace_line >>=
                 writeFile o

dump_strace :: FilePath -> FilePath -> IO ()
dump_strace i o = readFile i >>=
                  return . strace . parse >>=
                  return . render . pp_list . map pp_strace >>=
                  writeFile o


strace_is_exec :: Strace  -> Bool
strace_is_exec strace = strace_syscall strace =~ "^exec"
-- vm not shared
strace_is_clone_process :: Strace -> Bool
strace_is_clone_process  strace = strace_syscall strace =~ "^clone" &&
                                  not (any (=~ "CLONE_VM") (strace_args strace))
-- vm shared
strace_is_clone_thread :: Strace -> Bool
strace_is_clone_thread   strace = strace_syscall strace =~ "^clone" &&
                                  any (=~ "CLONE_VM") (strace_args strace)


strace_is_wait :: Strace -> Bool
strace_is_wait strace = strace_syscall strace =~ "^wait"



{-
************************************************************************
*                                                                      *
*              3. Pretty printers
*                                                                      *
************************************************************************
-}

instance Pretty StraceLine    where pp = text . show
instance Pretty Strace        where pp = pp_strace
instance Pretty ProcessState  where
        pp_summary  (PState vm strace pid) =
                pp_data "PState"
                [ ("pid"   , integer    pid)
                , ("strace", pp_summary strace)
                , ("vm"    , pp_summary vm)
                ]

instance Pretty VMAInfo       where
        pp_summary (VMAInfo prot flags fd offs trace) =
                pp_data "VMAInfo"
                [ ("prot"  , text prot)
                , ("flags" , text flags)
                , ("fd"    , text fd)
                , ("offset", text offs)
                , ("trace" , pp_summary trace)
                ]


instance Pretty ProcessTreeState where
        pp_summary (PTState psmap tidmap refmap timestamp) =
                pp_data "PTState"
                [ ("ps"  , pp_summary psmap)
                , ("tid" , pp_summary tidmap)
                , ("ref" , pp_summary refmap)
                , ("timestamp", pp_timestamp timestamp)
                ]



data IntervalRelation  = Region :~: ProcessState
                       deriving (Show)

instance Pretty IntervalRelation where
        pp       (iv :~: s) = pp iv <+> text ":~: s =" $$  pp rel
                where
                        rel   = section_translate (-x) $ (ps_vm s)
                        (x,y) = from_gen iv :: (Hyper Integer, Hyper Integer)

        pp_brief (iv :~: s) = pp iv <+> text ":~: s =" <+>  pp rel
                where
                        rel   = section_translate (-x) (ps_vm s)
                        (x,y) = from_gen iv



pp_strace_line :: StraceLine -> Doc
pp_strace_line l = text (show l)



pp_strace :: Strace -> Doc
pp_strace (Strace tid syscall args ret trace) =
        integer tid <+> text syscall <> parens (f args) <+> text "=" <+> text ret $$
        nest 5 (vcat (map (text . sl_call_stack) trace))
        where
                f = sep . punctuate comma . map text


pp_data_frame :: [PTState] -> Doc
pp_data_frame ss = header $$ body
        where
                header = text "t pid from to v trace_id"
                body   = vcat $ map pp_pt_data_frame ss

pp_pt_data_frame :: PTState -> Doc
pp_pt_data_frame s = vcat $ map pp_ps_data_frame' $ zip (repeat t) $ Map.toAscList (pt_ps_map s)
        where
                pp_ps_data_frame' (t, (pid, s)) = pp_ps_data_frame t pid s
                t = pt_timestamp s

pp_ps_data_frame :: Timestamp -> Pid -> PState -> Doc
pp_ps_data_frame t pid s = vcat $ map (prefix . pp_vma) $  section_to_asc_list (ps_vm s)
        where
                prefix doc = pp_timestamp t <+> integer pid <+> doc

pp_vma :: (Region, VMAInfo) -> Doc
pp_vma (i, v) = low i <+> high i <+> valuation v <+> trace_id v
        where
                -- R doesn't support 64-bit int!!
                -- So we represent a page by double's mantissa which is 52-bit
                low  = integer . to_page . hyper_std . gen_lower_bound :: Region -> Doc
                high = integer . to_page . hyper_std . gen_upper_bound :: Region -> Doc
                valuation = int . hash
                trace_id x = case vma_trace x of
                        Nothing      -> text "NA"
                        Just (id, _) -> int id

                to_page x = with_invariant (report "pp_vma::to_page" (x`rem` 2^12))
                            (at_page_boundary x)
                            (< 2^52)
                            $  x `div` 2^12

                at_page_boundary x = (x `rem` 2^12 == 0)


--
pp_trace ::  UniqueStrace -> Doc
pp_trace (n, Strace tid syscall args ret trace) = int n <+> (escape trace_doc)
        where
                args'       = hsep $ punctuate comma (map text args)
                funcall     = integer tid <+> text syscall <> parens args' <+> equals <+> text ret
                trace_lines = map sl_call_stack trace
                trace_doc   = vcat $ funcall : map text trace_lines
                escape s    = text $ show (render s)


{-
************************************************************************
*                                                                      *
*              4. Linux VM emulator
*                                                                      *
************************************************************************
-}

-- It's ok if page size is larger than this (as long as page_size == 2^n with n>=12)
page_shift = 12

type Pid = Integer
type Tid = Integer

data VMAInfo = VMAInfo
               { vma_prot   :: String
               , vma_flags  :: String
               , vma_fd     :: String
               , vma_offset :: String
               , vma_trace  :: Maybe UniqueStrace
               }
            deriving (Eq,Show)

instance Hashable VMAInfo where
        hashWithSalt n (VMAInfo a b c d _) = hashWithSalt n (a,b,c,d)

-- Any address can be made accessible by mprotect
vm_info_default  = VMAInfo "" "" "" "" Nothing :: VMAInfo

type Base    = Hyper Integer
type Region  = Generator Base
type VMA     = (Region, VMAInfo)
type VM      = Section Base VMAInfo

data ProcessState = PState
             { ps_vm      :: VM              -- ^ vm mapping
             , ps_strace  :: UniqueStrace    -- ^ the syscall that created this
             , ps_pid     :: Pid
             -- , process_env          :: [(String,String)] -- ^ @tbd
             }
             deriving (Eq,Show)

type PState  = ProcessState

ps_valid :: PState -> Bool
ps_valid (PState vm st pid) = section_valid vm && pid > 0

ps_empty :: Pid -> UniqueStrace -> PState
ps_empty pid strace = PState section_empty strace pid

ps_null_vm :: PState -> Bool
ps_null_vm s = section_null $ ps_vm s

ps_intersects :: Region -> PState -> Bool
ps_intersects region s = not $ section_null $ section_components_at region (ps_vm s)

ps_contained_in :: Region -> PState -> Bool
ps_contained_in region s  = section_lift2 f region' (ps_vm s) == region'
        where
                region' = section_singleton (region, True)
                f x y = x

type Timestamp = Integer

data RoseTree a = RoseTree a [RoseTree a]
                deriving (Eq,Show)

-- @tbd The whole state can and should be sheafified too
data ProcessTreeState = PTState
                        { pt_ps_map    :: Map Pid ProcessState
                        , pt_tid_map   :: Map Tid Pid
                        , pt_pid_ref   :: Map Pid Integer
                        , pt_timestamp :: Timestamp
                          -- @tbd
                          -- , ptree_tree :: RoseTree Pid
                        }
                      deriving (Eq,Show)

type PTState = ProcessTreeState

pt_valid :: PTState -> Bool
pt_valid (PTState { pt_ps_map = ps_map, pt_tid_map = tid_map, pt_pid_ref = ref_map }) =
        all is_valid_pid $ map_values tid_map
        where
                is_valid_pid pid = Map.member pid ps_map &&
                                   Map.member pid ref_map &&
                                   (ref_map ! pid) > 0

pt_empty :: ProcessTreeState
pt_empty  = PTState Map.empty Map.empty Map.empty 0

pt_null :: PTState -> Bool
pt_null (PTState ps_map tid_map ref_map _) = Map.null ps_map && Map.null tid_map && Map.null ref_map

pt_singleton :: UniqueStrace -> PTState
pt_singleton (n, strace) =
        with_invariant (printf "pt_singleton:(%d,%s)" n (show strace))
        (strace_is_exec strace)
        (not . pt_null)
        s
        where
                t   = fromIntegral n
                pid = strace_tid strace

                s = PTState
                    (Map.singleton pid (ps_empty pid (n,strace)))
                    (Map.singleton pid pid)
                    (Map.singleton pid 1)
                    t


pp_pt_head s = text $ show $ Map.toAscList (pt_ps_map s)

(.!) :: PTState -> Tid -> PState
s .! tid = with_invariant (printf "%s .! %d" (render $ pp_pt_head s) tid)
           (pt_member tid s)
           (const True)
           $ pt_ps_map s ! (pt_tid_map s ! tid)

pt_member :: Tid -> PTState -> Bool
pt_member tid (PTState ps_map tid_map ref_map stamp) =
        case Map.lookup tid tid_map of
        Just pid -> Map.member pid ps_map
        Nothing  -> False

pt_intersects :: Tid -> Region -> PTState -> Bool
pt_intersects tid region s = pt_member tid s  && ps_intersects region (s .! tid)

pt_act_vm :: (PState -> PState) -> Tid -> PTState -> PTState
pt_act_vm f tid s =
        with_invariant "pt_act_vm"
        precondition
        postcondition
        t
        where
                precondition  = pt_member tid s
                postcondition = pt_member tid

                pid    = ps_pid (s .! tid)
                ps_map = pt_ps_map s
                t      = s { pt_ps_map = map_adjust f pid ps_map }

-- |Create a new thread in the given process space
pt_insert_thread :: Tid -> Pid -> PTState -> PTState
pt_insert_thread tid pid s =
        with_invariant "pt_insert_thread"
        precondition
        postcondition
        t
        where
                precondition    = pt_valid s && not (pt_member tid s) && (pt_member pid s)
                postcondition s = pt_valid s && (pt_member tid s) && (s .! tid) == (s .! pid)

                tid_map  = pt_tid_map s
                ref_map  = pt_pid_ref s

                t       = s { pt_tid_map = Map.insert tid pid tid_map
                            , pt_pid_ref = Map.adjust (+1) pid ref_map
                            }

-- |Create a new process whose address space is the copy of the original
pt_insert_process :: Pid -> Pid -> UniqueStrace -> PTState -> PTState
pt_insert_process child_pid parent_pid strace s =
        with_invariant (report "pt_insert_process" (child_pid, parent_pid, t))
        precondition
        postcondition
        t
        where
                precondition    = pt_valid s && not (pt_member child_pid s) && (pt_member parent_pid s)
                postcondition s = pt_valid s &&
                                  (pt_member child_pid s) &&
                                  (ps_vm $ s .! child_pid) == (ps_vm $ s .! parent_pid) &&
                                  ps_pid (s .! child_pid) == child_pid

                ps_map  = pt_ps_map s
                tid_map = pt_tid_map s
                ref_map = pt_pid_ref s

                parent_ps = s .! parent_pid
                child_ps  = parent_ps { ps_pid = child_pid, ps_strace = strace }

                t         = s { pt_ps_map  = Map.insert child_pid child_ps  ps_map
                              , pt_tid_map = Map.insert child_pid child_pid tid_map
                              , pt_pid_ref = Map.insert child_pid 1 ref_map
                              }


pt_update_time :: Timestamp -> PTState -> PTState
pt_update_time t s = s { pt_timestamp = t}

-- |Main VMA emulator function
emulate_vma :: [(Id,Strace)] -> [PTState]
emulate_vma syscalls =
        with_invariant (printf "emulate_vma:%s" (show $ take 10 syscalls))
        precondition
        postcondition
        $  scanl action (pt_singleton (head syscalls)) (tail syscalls)

        where
                precondition    = length syscalls > 0
                postcondition s = length s > 0

                action s (n,syscall) = let t = fromIntegral n -- @tbd: use genuine timestamp
                                       in  pt_update_time t $ pt_action s (n,syscall) :: PTState




ps_paged :: PState -> Bool
ps_paged s = all paged' $ section_domain_asc (ps_vm s)
        where
                mask = 1 `shiftL` page_shift - 1

                paged' iv = let (x,y) = from_gen iv
                                (a,b) = (hyper_std x, hyper_std y)
                            in
                                    a .&. mask == 0 && b .&. mask == 0

pt_paged :: PTState -> Bool
pt_paged (PTState { pt_ps_map = map}) = all ps_paged $ map_values map

region :: Integer -> Integer -> Region
region p len = align_page $ gen (h(p)-dx, h(p) + h(len) -dx)
        where h = fromIntegral

align_page :: Region -> Region
align_page i = let (x,y)         = from_gen i
                   align_floor x = (x `shiftR` page_shift) `shiftL` page_shift
                   align_ceil  x = (x `shiftR` page_shift + 1) `shiftL` page_shift
               in
                       gen (align_floor x, align_ceil y)

type MmapFlags = (String, String, String, String)

ps_act_vm :: (VM -> VM)  -> PState -> PState
ps_act_vm f s = s { ps_vm = f (ps_vm s) }

ps_area :: PState -> Hyper Integer
ps_area = section_area . ps_vm

vma_valid :: Region -> Bool
vma_valid g = let x = gen_lower_bound g
                  y = gen_upper_bound g
              in
                      hyper_d x < 0 &&
                      hyper_d y < 0 &&
                      hyper_std x `rem` 2^12 == 0 &&
                      hyper_std y `rem` 2^12 == 0

ps_insert_vma :: Region ->  MmapFlags -> UniqueStrace -> PState -> PState
ps_insert_vma g (prot,flags,fd,offset) trace s =
        with_invariant (report "ps_insert_vma" (g, g /\ s, ps_area s, ps_area t))
        precondition
        postcondition
        t
        where
                precondition    = vma_valid g
                postcondition t = section_area (g/\s) == gen_area g || ps_area t > ps_area s

                t = ps_act_vm (fromJust . section_glue_at g vmainfo) $ ps_delete_vma g trace s
                vmainfo = VMAInfo prot flags fd offset (Just trace)

                g /\ s = section_lift2 const (ps_vm s) (section_singleton (g,Singleton))


-- | 'Region' given may not intersect the section (in which case it's just a no-op)
ps_delete_vma :: Region -> UniqueStrace -> PState -> PState
ps_delete_vma g trace s =
        with_invariant (report "ps_delete_vma" (g, trace, s))
        precondition
        postcondition
        t
        where
                precondition = vma_valid g
                postcondition t = ps_area s >= ps_area t

                t =  ps_act_vm (restrict_compl g) s

                restrict_compl g vm = let s1 = head $ gen_compliments g
                                      in  section_lift2 const vm s1


vm_diff :: VM -> VM -> VM
vm_diff x y =
        with_invariant "vm_diff"
        precondition
        postcondition
        x'
        where
                precondition = True
                postcondition x' = section_disjoint x y || section_area x > section_area x'

                xy  = section_lift2 const x  y
                xy' = head $ section_compliments xy

                x' = section_lift2 const x  xy'


-- |See mprotect(2)
ps_update_vma :: Region -> String -> UniqueStrace -> PState -> PState
ps_update_vma g prot trace s =
        with_invariant (report "ps_update_vma" (g,trace,ps_area s, ps_area t))
        precondition
        postcondition
        t
        where
                precondition = vma_valid g && ps_valid s
                postcondition t = ps_area t >= ps_area s

                t  = ps_act_vm f s

                f vm = (s0 - vm) \/ (vm /\ s0) \/ (vm - s0)
                s0 = section_singleton (g, default_vma)

                (-)    = vm_diff
                x \/ y = fromJust $ section_glue x y
                x /\ y = section_lift2 (\x y -> update x) x y

                update vma  = vma { vma_prot = prot , vma_trace = Just trace  }
                default_vma = update vm_info_default


-- |VMA state transition function for processes
-- Use sequence number to identify stack traces
ps_action :: PState -> UniqueStrace -> PState
ps_action s t@(n, Strace tid "mmap"     args ret trace) = ps_mmap     s args ret t
ps_action s t@(n, Strace tid "munmap"   args ret trace) = ps_munmap   s args ret t
ps_action s t@(n, Strace tid "mprotect" args ret trace) = ps_mprotect s args ret t
ps_action s t@(n, Strace tid "brk"      args ret trace) = ps_brk      s args ret t
ps_action s t = pp_error $ text "ps_action:unsupported syscall -- please improve this" $$ pp t $$ pp s


-- |VMA state transition function for process trees
pt_action :: PTState -> UniqueStrace -> PTState
pt_action s (n, t@(Strace tid syscall args ret trace))
        | strace_is_exec t           = pt_exec          tid s args ret (n,t)
        | strace_is_clone_process t  = pt_clone_process tid s args ret (n,t)
        | strace_is_clone_thread  t  = pt_clone_thread  tid s args ret (n,t)
        | strace_syscall t == "exit" = pt_exit          tid s args ret (n,t)
        | ignored_call t             = s
        | otherwise                  = pt_act_vm (ps_action' (n,t)) tid s
        where
                ps_action' = flip ps_action
                ignored_call t = strace_syscall t =~ "^(wait|exit_group|arch_prctl)" :: Bool

ps_mmap :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_mmap s [addr, length, prot, flags, fd, offset] ret trace =
        let p    = read ret    :: Integer
            len  = read length :: Integer
            anon = "MAP_ANON" `isInfixOf` flags  :: Bool
        in
                ps_insert_vma (region p len) (prot, flags, fd, offset) trace s

-- |Let's just assume the data segment starts at zero..
ps_brk :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_brk s [_] ret trace = ps_insert_vma (region p len) ("", "", "", "") trace s
        where
                p   = 0
                len = read ret

ps_munmap :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_munmap s [addr, length] ret trace =
        let p   = read addr   :: Integer
            len = read length :: Integer
        in
                ps_delete_vma (region p len) trace s

{-
MPROTECT(2)
NOTES
       On  Linux  it  is  always  permissible to call mprotect() on any address in a process's address space
       (except for the kernel vsyscall area).  In particular it can be used to change existing code mappings
       to be writable.
-}
ps_mprotect :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_mprotect s [addr, length, prot] ret trace =
        with_invariant desc precondition postcondition s'
        where
                desc            = report "ps_mprotect" (pp $ region p len :~: s, pp trace, pp s)
                precondition    = read ret == 0 && strace_syscall (snd trace) == "mprotect"
                postcondition s = (region p len) `ps_contained_in` s

                p   = read addr   :: Integer
                len = read length :: Integer

                s'  = ps_update_vma (region p len) prot trace s





pt_exec :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_exec tid s args ret (n,strace) =
        with_invariant "pt_exec" precondition postcondition s'
        where
                precondition    = pt_member tid s && tid == strace_tid strace && ret == "0"
                postcondition s = pt_member tid s && ps_null_vm (s .! tid)

                s' = pt_act_vm (const $ ps_empty tid (n, strace)) tid s


pt_clone_thread :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_clone_thread tid s args ret strace =
        with_invariant "pt_clone_thread" precondition postcondition s'
        where
                precondition    = pt_member tid  s && not (pt_member tid' s) && tid' /= (-1)
                postcondition s = pt_member tid' s &&
                                  not (ps_null_vm (s .! tid')) &&
                                  (s .! tid) /= (s .! tid')

                pid  = ps_pid (s .! tid)
                tid' = read ret :: Tid
                s'   = pt_insert_thread tid' pid s


pt_clone_process :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_clone_process tid s args ret strace =
        with_invariant "pt_clone_process" precondition postcondition s'
        where
                precondition    = pt_member tid  s && not (pt_member child_pid s) && child_pid /= (-1)
                postcondition s = pt_member child_pid s &&
                                  not (ps_null_vm (s .! child_pid))  &&
                                  (ps_vm $ s .! tid) == (ps_vm $ s .! child_pid)

                child_pid  = read ret :: Pid
                parent_pid = ps_pid (s .! tid )
                s'         = pt_insert_process child_pid parent_pid strace s


pt_exit :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_exit tid s args ret strace =
        pt_delete_thread tid s

-- Let's ignore for the moment
pt_wait :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_wait tid s args ret strace = s

pt_delete_thread :: Tid -> PTState -> PTState
pt_delete_thread tid s =
        with_invariant "pt_delete_thread"
        precondition
        postcondition
        t
        where
                precondition = pt_member tid s && count > 0
                postcondition s = not $ pt_member tid s

                psmap   = pt_ps_map s
                tidmap  = pt_tid_map s
                refmap  = pt_pid_ref s

                pid   = tidmap ! tid
                count = refmap ! pid

                t | count == 1 = s { pt_ps_map  = Map.delete pid psmap
                                   , pt_tid_map = Map.delete tid tidmap
                                   , pt_pid_ref = Map.delete pid refmap
                                   }
                  | count > 1  = s { pt_tid_map = Map.delete tid tidmap
                                   , pt_pid_ref = Map.adjust dec pid refmap
                                   }

                dec x = x -1

{-
************************************************************************
*                                                                      *
*              5. Utilities
*                                                                      *
************************************************************************
-}

chomp            = strip_left . strip_right
strip_right_if p = reverse . strip_left_if p . reverse
strip_left_if  p = dropWhile p
strip_right      = strip_right_if isSpace
strip_left       = strip_left_if  isSpace


map_keys   = map fst . Map.toList
map_values = map snd . Map.toList
map_adjust f k m = with_invariant "map_adjust" (Map.member k m) (Map.member k) $ Map.adjust f k m



snapshot n xs
        | n <= 0    = error "snapshot:n<=0"
        | otherwise = every (ceiling (len xs / n)) xs
        where len = fromIntegral . length

every n xs
        | n <= 0    = error message
        | otherwise = map head' $ chunksOf n xs
        where
                head'   = head . assert' message  (not . null)
                message = printf "every:%d:%s" n (show $ take 10 xs)


(><) :: Monad m => (c -> m a) -> (c -> m b) -> (c -> m (a,b))
(m >< n) x = do a <- m x
                b <- n x
                return (a,b)

(***) :: Monad m => (c -> m a) -> (d -> m b) -> ((c,d) -> m (a,b))
(m *** n) (x,y) = do a <- m x
                     b <- n y
                     return (a,b)


{-
************************************************************************
*                                                                      *
*              6. Testing and debugging
*                                                                      *
************************************************************************
-}


test_memst :: IO ()
test_memst =  readFile test_file                         >>=
              return . parse                             >>=
              return . strace_with_id                    >>=
              return . emulate_vma                       >>=
              return . snapshot 100                      >>=
              return . take 10                           >>=
              putStrLn . render . pp_list . map (text . show)


test_matrix :: IO ()
test_matrix =  readFile test_file                         >>=
               return . parse                             >>=
               return . strace_with_id                    >>=
               return . emulate_vma                       >>=
               return . snapshot 100                      >>=
               return . take 10                           >>=
               putStrLn . render . pp_data_frame



test_file   = "build/data-2016-11-16_17h37m26s/strace.data" -- "cassandra.strace"
matrix_file = "out.data"
trace_file  = "trace.data"

test = dump test_file matrix_file trace_file

-- trace without syscall line "/lib/x86_64-linux-gnu/libc-2.19.so(madvise+0x7) [0xf4967]
test_strace :: IO ()
test_strace =  readFile test_file      >>=
               return . parse  >>=
               return . strace >>=
               return . take 100 >>=
               putStrLn . render . pp_list . map pp_strace

test_parse :: IO ()
test_parse  =  getContents >>=
               return . parse >>=
               print


{-
************************************************************************
*                                                                      *
*              7. IO
*                                                                      *
************************************************************************
-}


read_strace :: FilePath -> IO ([PTState], [UniqueStrace])
read_strace in_file =  readFile in_file        >>=
                       return . parse          >>=
                       return . strace_with_id >>=
                       ((return . emulate_vma) >< (return . id))


write_data_frame :: FilePath -> [PTState] -> IO ()
write_data_frame file ss =  writeFile file $ render $ pp_data_frame ss


write_stack_trace :: FilePath -> [UniqueStrace] -> IO ()
write_stack_trace file ts  = let header = text "trace_id trace"
                                 body   = vcat (map pp_trace ts)
                                 doc    = header $$ body
                             in
                                     writeFile file $ render doc



dump :: FilePath -> FilePath -> FilePath -> IO ()
dump strace_in frame_out trace_out =
        read_strace strace_in >>=
       ((write_data_frame frame_out . summarize) ***  write_stack_trace trace_out ) >> return ()

        where
                summarize = assert' "valid" (all pt_valid) . snapshot 1000


parse_opts :: String -> [String] -> IO (FilePath, FilePath, FilePath)
parse_opts prog_name xs =
        let opts       = map parse_a_opt xs
            help       = lookup_all "help"   opts
            strace_ins = lookup_all ""       opts
            frame_outs = lookup_all "output" opts
            trace_outs = lookup_all "trace"  opts

        in
                case (help,
                      strace_ins,
                      frame_outs,
                      trace_outs) of
                ([],
                 [strace_in],
                 [frame_out],
                 [trace_out]) ->
                        return (strace_in, frame_out, trace_out)
                _ ->
                        show_help prog_name xs
        where
                parse_a_opt x = let long_match  =  x =~ "^--([^=]+)=(.*)$"  :: [[String]]
                                    plain_match =  x =~ "^([^-].*)$"        :: [[String]]
                                in
                                        case (long_match, plain_match) of
                                        ([[_,opt,val]], _ ) -> (opt, val)
                                        (_ , [[_,val]])     -> ("" , val)
                                        _                 -> error $ "unknown option:" ++ x

                lookup_all key assoc_list = map snd $ filter (\(x,y) -> x == key) assoc_list

show_help :: String -> [String] -> IO a
show_help prog_name args = do putStrLn $ printf help_template prog_name
                              exitSuccess
        where
                help_template = "Usage:%s [--help] STRACE_IN --output=FRAME_OUT --trace=TRACE_OUT"

main :: IO ()
main = do prog_name <- getProgName
          args      <- getArgs
          (strace_in, frame_out, trace_out) <- parse_opts prog_name args
          putStrLn $ show (strace_in, frame_out, trace_out)
          dump strace_in frame_out trace_out
