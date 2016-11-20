{-
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
5. A hyperreal ring <1,dx,1/dx>
6. Utilities
7. Testing and debugging
8. IO

Note: all the functions are in underscore_case to distinguish them from
      the library functions (also because I like kernel code).

Bug: if a child pid has been recycled during the process's liftime,
     the behavior is undefined.

-}

module Main
where

import Numeric

import Data.Maybe
import Data.List
import Data.List.Split
import Data.Char
import Data.Hashable
import Data.Bits

import           Data.Map (Map, (!))
import qualified Data.Map as Map
import           Data.IntervalMap          (IntervalMap)
import qualified Data.IntervalMap          as IntervalMap
import           Data.IntervalMap.Interval (Interval)
import qualified Data.IntervalMap.Interval as Interval
-- for pretty printing without ghc extension
import qualified Data.IntervalMap.Generic.Strict as StrictIntervalMap


import Control.Exception

import Text.Printf
import Text.PrettyPrint
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
parse_signal x = let matches = x  =~ "^ *(\\d+) --- *(\\w+) *{(.*)} *--- *$" :: [[String]]
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
        ++ show call_stack ++ (render $ pp_list $ map pp_line $ take 30 rest)

-- Skip
strace (Exit   tid status: rest)      =
        let (traces, rest') = trace_lines rest
        in  strace rest'
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
                 return . render . pp_list . map pp_line >>=
                 writeFile o

dump_strace :: FilePath -> FilePath -> IO ()
dump_strace i o = readFile i >>=
                  return . strace . parse >>=
                  return . render . pp_list . map pp_strace >>=
                  writeFile o


{-
************************************************************************
*                                                                      *
*              3. Pretty printers
*                                                                      *
************************************************************************
-}

-- |Rule: never require fancy extensions
class Pretty a where
        pp         :: a -> Doc
        pp         = pp_summary
        pp_summary :: a -> Doc
        pp_summary = pp
        pp_brief   :: a -> Doc
        pp_brief   = pp_summary

-- |Report a summary of the data
report :: Pretty a => String -> a -> String
report desc d = render $ text desc <> colon $$ nest 2 (pp_summary d) $$ text "END_REPORT\n"

-- |Report  data
report_full :: Pretty a => String -> a -> String
report_full desc d = render $ text desc <> colon $$ nest 2 (pp d) $$ text "END_FULL_REPORT\n"

-- | Pretty error reporting
pp_error :: Doc -> a
pp_error = error . render


instance Pretty Doc     where pp = id
instance Pretty Int     where pp = text . show
instance Pretty Integer where pp = text . show
instance (Show a, Integral a) => Pretty (IntervalMap.Interval a) where
        pp iv = pp_hyper_interval $ hex  $ hyper iv
                where hex (x,y) = (fmap Hex x, fmap Hex y)

pp_hyper_interval :: Pretty a => (Hyper a, Hyper a) -> Doc
pp_hyper_interval (x,y) = parens $ pp x <> comma <>  pp y

instance Pretty a => Pretty (Hyper a) where
        pp (Hyper is x es) = pp_polynomial (infs ++ dxs)
                where
                        infs = reverse (monomials "inf" (x:is))
                        dxs  = tail    (monomials "dx" (0:es))

type Monomial a = (a, String, Integer)

monomials x cs = zip3 cs (repeat x) [0..]
monomial_null (c,x,d) = c == 0

pp_polynomial :: Num a => [Monomial a] -> Doc
pp_polynomial = pp_polynomial' . filter (not . monomial_null)
        where
                pp_polynomial' [] = int 0
                pp_polynomial' (m:ms) = pp_monomial m <> cat (map pp_monomial_sign ms)

pp_monomial :: Monomial a -> Doc
pp_monomial (coeff,x,deg)
        | coeff == 0  = int 0
        | deg   == 0  = text (show coeff)
        | otherwise   = text (show coeff) <> text x <> "^" <> text (show deg)

pp_monomial_sign m@(coeff, x, deg)
        | coeff > 0 = text "+" <> pp_monomial m
        | otherwise = pp_monomial m


instance (Pretty a, Pretty b) => Pretty(a,b) where
        pp         (a,b) = pp_tuple [pp         a, pp         b]
        pp_summary (a,b) = pp_tuple [pp_summary a, pp_summary b]

instance (Pretty a, Pretty b, Pretty c) => Pretty(a,b,c) where
        pp         (a,b,c) = pp_tuple [pp         a, pp         b, pp         c]
        pp_summary (a,b,c) = pp_tuple [pp_summary a, pp_summary b, pp_summary c]

instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty(a,b,c,d) where
        pp         (a,b,c,d) = pp_tuple [pp         a, pp         b, pp         c, pp         d]
        pp_summary (a,b,c,d) = pp_tuple [pp_summary a, pp_summary b, pp_summary c, pp_summary d]

instance Pretty a => Pretty [a] where
        pp         = pp_list . map pp
        pp_summary = pp_list . add_ellipsis . map pp_summary . take 10
                     where add_ellipsis ps = ps ++ [text "..."]


instance (Pretty k, Pretty v) => Pretty (Map k v) where
        pp         m = text "Map.fromList" <+> pp         (Map.toAscList m)
        pp_summary m = text "Map.fromList" <+> pp_summary (Map.toAscList m)

instance (Pretty k, Pretty v) => Pretty (StrictIntervalMap.IntervalMap k v) where
        pp         m = text "IntervalMap.fromList" <+> pp         (IntervalMap.toAscList m)
        pp_summary m = text "IntervalMap.fromList" <+> pp_summary (IntervalMap.toAscList m)

instance Pretty StraceLine    where pp = text . show
instance Pretty Strace        where pp = pp_strace
instance Pretty ProcessState  where
        pp         (PState tree strace pid)= pp_data "PState" [integer pid, pp strace, pp         tree]
        pp_summary (PState tree strace pid)= pp_data "PState" [integer pid, pp strace, pp_summary tree]

instance Pretty VMAInfo       where
        pp         (VMAInfo prot flags fd offs trace) =
                pp_data "VMAInfo" [ text prot, text flags, text fd, text offs, pp trace ]

        pp_summary (VMAInfo prot flags fd offs trace) =
                pp_data "VMAInfo" [ text prot, text flags, text fd, text offs, pp_summary trace ]


newtype Hex a = Hex a
instance (Integral a, Show a) => Show   (Hex a) where
        show (Hex x) =  sign x ++ "0x" ++ showHex (abs x) ""
                        where sign x | x >= 0    = ""
                                     | otherwise = "-"

instance (Integral a, Show a) => Pretty (Hex a)  where pp = text . show


data IntervalRelation  = Region :~: ProcessState
                       deriving (Show)

instance Pretty IntervalRelation where
        pp       (iv :~: s) = pp iv <+> text ":~: s =" $$  pp rel
                where
                        rel = imap_z_act (-x) $ (ps_vma_tree s)
                        x   = Interval.lowerBound iv

        pp_brief (iv :~: s) = pp iv <+> text ":~: s =" <+>  pp rel
                where
                        rel = map (z_act_left (-x)) $ imap_keys (ps_vma_tree s)
                        x   = Interval.lowerBound iv

-- |Should satisfy the obvious laws
class ZSet a where
        z_act_left  :: Integer -> a -> a
        z_act_left = flip z_act_right
        z_act_right :: a -> Integer -> a
        z_act_right = flip z_act_left

instance (ZSet a,ZSet b) =>  ZSet (a,b) where
        z_act_left  g (a,b) = (z_act_left  g a, z_act_left  g b)
        z_act_right (a,b) g = (z_act_right a g, z_act_right b g)

instance Num a => ZSet (Hyper a) where
        z_act_left x i = fromIntegral x + i

instance Num a => ZSet (IntervalMap.Interval a) where
        z_act_left x iv = from_hyper $ z_act_left x (hyper iv)

-- Can't generalize without extension
imap_z_act :: Integer -> VMATree -> VMATree
imap_z_act x m  = IntervalMap.fromList $ map act $ IntervalMap.toList m
        where act (k,v) = (z_act_left x k, v)


pp_line :: StraceLine -> Doc
pp_line l = text (show l)

pp_list :: [Doc] -> Doc
pp_list = brackets . cat . punctuate comma

pp_tuple :: [Doc] -> Doc
pp_tuple = parens . cat . punctuate comma

pp_data :: String -> [Doc] -> Doc
pp_data constr body = text constr <+> braces (cat $ punctuate comma body)

pp_timestamp = integer



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
pp_ps_data_frame t pid s = vcat $ map (prefix . pp_vma) $  IntervalMap.toAscList (ps_vma_tree s)
        where
                prefix doc = pp_timestamp t <+> integer pid <+> doc

pp_vma :: (Region, VMAInfo) -> Doc
pp_vma (i, v) = low i <+> high i <+> valuation v <+> trace_id v
        where
                -- R doesn't support 64-bit int!!
                -- Represent a page by double's mantissa which is 52-bit
                low  = integer . to_page . Interval.lowerBound :: Region -> Doc
                high = integer . to_page . Interval.upperBound :: Region -> Doc
                valuation = int . hash
                trace_id  = int . fst . vma_trace

                to_page x = with_invariant "pp_vma::to_page"
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

type Region  = IntervalMap.Interval Integer
type VMA     = (Region, VMAInfo)
type VMATree = IntervalMap Integer VMAInfo

-- |Acts on *points* not just intervals
vm_update :: (VMAInfo -> VMAInfo) -> Region -> VMATree -> VMATree
vm_update f region vm =
        with_invariant "vm_update"
        precondition
        postcondition
        $ vm'
        where
                precondition     = disjoint_interval_tree vm && not (interval_null region)
                postcondition vm = disjoint_interval_tree vm

                v0     = IntervalMap.singleton (region, vm_info_default)
                vm'    = lift_sheaf2 f' vm v0
                f' x _ = f x


imap_as_list :: ([(Region, VMAInfo)] -> [(Region, VMAInfo)]) -> VMATree -> VMATree
imap_as_list f = IntervalMap.fromList . f . IntervalMap.toList

data ProcessState = PState
             { ps_vma_tree  :: VMATree            -- vm mapping
             , ps_strace    :: UniqueStrace       -- the syscall that created this
             , ps_pid       :: Pid
             -- @tbd
             -- , process_env          :: [(String,String)]
             }
             deriving (Eq,Show)

type PState  = ProcessState

ps_empty :: Pid -> UniqueStrace -> PState
ps_empty pid strace = PState (IntervalMap.empty) strace pid

ps_null_vma :: PState -> Bool
ps_null_vma s = IntervalMap.null $ ps_vma_tree s

ps_intersects :: Region -> PState -> Bool
ps_intersects region s = not $ IntervalMap.null $ IntervalMap.intersecting (ps_vma_tree s) region

ps_contained_in :: Region -> PState -> Bool
ps_contained_in region s  = let relevant_tree = IntervalMap.intersecting (ps_vma_tree s) region
                            in  any (`Interval.subsumes` region) $ imap_keys relevant_tree


type Timestamp = Integer

data RoseTree a = RoseTree a [RoseTree a]
                deriving (Eq,Show)

data ProcessTreeState = PTState
                        { pt_ps_map    :: Map Pid ProcessState
                        , pt_tid_map   :: Map Tid Pid
                        , pt_timestamp :: Timestamp
                          -- @tbd
                          -- , ptree_tree :: RoseTree Pid
                        }
                      deriving (Eq,Show)

type PTState = ProcessTreeState

pt_valid :: PTState -> Bool
pt_valid (PTState { pt_ps_map = ps_map, pt_tid_map = tid_map }) =
        all is_valid_pid $ map_values tid_map
        where is_valid_pid tid = Map.member tid ps_map

pt_empty :: ProcessTreeState
pt_empty  = PTState Map.empty Map.empty 0

pt_null :: PTState -> Bool
pt_null (PTState ps_map tid_map _) = Map.null ps_map && Map.null tid_map

pt_singleton :: UniqueStrace -> PTState
pt_singleton (n, strace) =
        with_invariant (printf "pt_singleton:(%d,%s)" n (show strace))
        (is_exec strace)
        (not . pt_null)
        $ PTState (Map.singleton pid (ps_empty pid (n,strace))) (Map.singleton pid pid) t
        where
                t   = fromIntegral n
                pid = strace_tid strace


pp_pt_head s = text $ show $ Map.toAscList (pt_ps_map s)

(.!) :: PTState -> Tid -> PState
s .! tid = with_invariant (printf "%s .! %d" (render $ pp_pt_head s) tid)
           (pt_member tid s)
           (const True)
           $ pt_ps_map s ! (pt_tid_map s ! tid)

pt_member :: Tid -> PTState -> Bool
pt_member tid (PTState ps_map tid_map _) =
        case Map.lookup tid tid_map of
        Just pid -> Map.member pid ps_map
        Nothing  -> False

pt_intersects :: Tid -> Region -> PTState -> Bool
pt_intersects tid region s = (pt_member tid s)  && ps_intersects region (s .! tid)

pt_adjust :: (PState -> PState) -> Tid -> PTState -> PTState
pt_adjust f tid s =
        with_invariant "pt_adjust" precondition postcondition s'
        where
                precondition  = pt_member tid s
                postcondition = pt_member tid

                pid    = ps_pid (s .! tid)
                ps_map = pt_ps_map s
                s'     = s { pt_ps_map = map_adjust f pid ps_map }



-- |Create a new thread in the given process space
pt_insert_thread :: Tid -> Pid -> PTState -> PTState
pt_insert_thread tid pid s =
        with_invariant "pt_insert_thread" precondition postcondition s'
        where
                precondition    = pt_valid s && not (pt_member tid s) && (pt_member pid s)
                postcondition s = pt_valid s && (pt_member tid s) && (s .! tid) == (s .! pid)

                tid_map  = pt_tid_map s
                tid_map' = Map.insert tid pid tid_map
                s'       = s { pt_tid_map = tid_map' }

-- |Create a new process whose address space is the copy of the original
pt_insert_process :: Pid -> Pid -> PTState -> PTState
pt_insert_process child_pid parent_pid s =
        with_invariant "pt_insert_process" precondition postcondition s'
        where
                precondition    = pt_valid s && not (pt_member child_pid s) && (pt_member parent_pid s)
                postcondition s = pt_valid s &&
                                  (pt_member child_pid s) &&
                                  (s .! child_pid) == (s .! parent_pid) &&
                                  ps_pid (s .! child_pid) == child_pid

                PTState ps_map tid_map _  = s
                ps_map'  = Map.insert child_pid (s .! parent_pid) ps_map
                tid_map' = Map.insert child_pid child_pid tid_map
                s'       = s { pt_ps_map = ps_map' , pt_tid_map = tid_map' }


pt_update_time :: Timestamp -> PTState -> PTState
pt_update_time t s = s { pt_timestamp = t}

-- |Main VMA emulator function
emulate_vma :: [(Id,Strace)] -> [PTState]
emulate_vma syscalls =
        with_invariant (printf "emulate_vma:%s" (show $ take 10 syscalls))
        (length syscalls > 0)
        (\ss -> length ss > 0)
        $  scanl action (pt_singleton (head syscalls)) (tail syscalls)

        where
                action s (n,syscall) = let t = fromIntegral n -- @tbd: use genuine timestamp
                                       in  pt_update_time t $ pt_action s (n,syscall) :: PTState


ps_disjoint :: PState -> Bool
ps_disjoint PState { ps_vma_tree = tree } = disjoint_interval_tree tree

pt_disjoint :: PTState -> Bool
pt_disjoint PTState { pt_ps_map = map } = all ps_disjoint $ map_values map

disjoint_interval_tree :: VMATree -> Bool
disjoint_interval_tree tree = all disjoint' $ rel  $ IntervalMap.keys tree
        where
                rel xs = zip xs (tail xs)
                disjoint'  (i, j) = let (x,y) = hyper i
                                        (z,w) = hyper j
                                    in  y <= z || w <= x

ps_paged :: PState -> Bool
ps_paged s = all paged' $ IntervalMap.keys (ps_vma_tree s)
        where
                mask = 1 `shiftL` page_shift - 1

                paged' iv = let (x,y) = hyper iv
                                (a,b) = (hyper_std x, hyper_std y)
                            in
                                    a .&. mask == 0 && b .&. mask == 0

pt_paged :: PTState -> Bool
pt_paged (PTState { pt_ps_map = map}) = all ps_paged $ map_values map

region :: Integer -> Integer -> Region
region p len = IntervalMap.IntervalCO p (p+len)

align_page :: Region -> Region
align_page i = let (x,y)         = hyper i
                   align_floor x = (x `shiftR` page_shift) `shiftL` page_shift
                   align_ceil  x = (x `shiftR` page_shift + 1) `shiftL` page_shift
               in
                       from_hyper (align_floor x, align_ceil y)

type MmapFlags = (String, String, String, String)

ps_insert_vma :: (Integer, Integer) ->  MmapFlags -> UniqueStrace -> PState -> PState
ps_insert_vma (p,len) (prot,flags,fd,offset) trace s =
        with_invariant "insert_vma" precondition postcondition s''

        where
                precondition    = ps_disjoint s && ps_paged s
                postcondition s = ps_disjoint s && ps_paged s

                s'           = ps_delete_vma (p,len) trace s
                iv           = align_page $ region p len
                tree'        =  IntervalMap.insert
                                iv
                                (VMAInfo prot flags fd offset trace)
                                (ps_vma_tree s') :: IntervalMap Integer VMAInfo
                s''          = s { ps_vma_tree = tree' }

pt_insert_vma :: Tid -> (Integer, Integer) -> MmapFlags -> UniqueStrace -> PTState -> PTState
pt_insert_vma tid region flags trace s =
        with_invariant "pt_insert_vma"  precondition  postcondition s'

        where
                precondition  = pt_member tid s
                postcondition = pt_member tid

                ps_map  = pt_ps_map s
                tid_map = pt_tid_map s

                s' =  pt_adjust (ps_insert_vma region flags trace) tid s


ps_delete_vma :: (Integer, Integer) -> UniqueStrace -> PState -> PState
ps_delete_vma (p,len) trace s =
        with_invariant "delete_vma" precondition postcondition s'

        where
                precondition    = ps_disjoint s && ps_paged s
                postcondition s = ps_disjoint s && ps_paged s

                iv    = align_page $ region p len

                tree' = let (below, cross, above) = IntervalMap.splitIntersecting (ps_vma_tree s) iv
                            cross_list            = IntervalMap.toAscList cross
                            cross_list'           = concat $ map del cross_list
                            cross'                = IntervalMap.fromList cross_list'
                        in
                                below \/ cross' \/ above

                s'    = s { ps_vma_tree = tree' }

                del =  uncurry zip . ((`interval_diff` iv) >< repeat)
                       :: (Region, VMAInfo) -> [(Region,VMAInfo)]

                (f >< g) (x,y) = (f x, g y)


pt_delete_vma :: Tid -> (Integer, Integer) -> UniqueStrace -> PTState -> PTState
pt_delete_vma tid (p,len) trace s =
        with_invariant "pt_delete_vma" precondition postcondition s'
        where
                precondition  = pt_member tid s
                postcondition = not . pt_intersects tid (region p len)

                s' = pt_adjust (ps_delete_vma (p,len) trace) tid s


-- |See mprotect(2)
ps_update_vma :: (Integer, Integer) -> String -> UniqueStrace -> PState -> PState
ps_update_vma (p,len) prot trace s =
        with_invariant desc precondition postcondition s'
        where
                desc            = report_full "ps_update_vma" ((region p len), trace, s)
                precondition    = p > 0 && len > 0
                postcondition s = (region p len) `ps_contained_in` s

                tree'      = vm_update update (region p len) (ps_vma_tree s)
                update vma = Just vma { vma_prot = prot , vma_trace = trace  }
                s'         = s { ps_vma_tree = tree' }


-- |VMA state transition function for processes
-- Use sequence number to identify stack traces
ps_action :: PState -> UniqueStrace -> PState
ps_action s t@(n, Strace tid "mmap"     args ret trace) = ps_mmap     s args ret t
ps_action s t@(n, Strace tid "munmap"   args ret trace) = ps_munmap   s args ret t
ps_action s t@(n, Strace tid "mprotect" args ret trace) = ps_mprotect s args ret t
ps_action s t@(n, Strace tid "brk"      args ret trace) = ps_brk      s args ret t

-- Ignore
ps_action s t@(n, strace) | strace_syscall strace == "arch_prctl" = s

ps_action s t = pp_error $ text "ps_action:unsupported syscall -- please improve this" $$ pp t $$ pp s


-- |VMA state transition function for process trees
pt_action :: PTState -> UniqueStrace -> PTState
pt_action s (n, t@(Strace tid syscall args ret trace))
        | is_exec t           = pt_exec          tid s args ret (n,t)
        | is_clone_process t  = pt_clone_process tid s args ret (n,t)
        | is_clone_thread  t  = pt_clone_thread  tid s args ret (n,t)
        | otherwise           = pt_adjust (ps_action' (n,t)) tid s
        where
                ps_action' = flip ps_action


ps_mmap :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_mmap s [addr, length, prot, flags, fd, offset] ret trace =
        let p    = read ret    :: Integer
            len  = read length :: Integer
            anon = "MAP_ANON" `isInfixOf` flags  :: Bool
        in
                ps_insert_vma (p,len) (prot, flags, fd, offset) trace s

-- |Let's just assume the data segment starts at zero..
ps_brk :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_brk s ["NULL"] ret trace = ps_insert_vma (p,len) ("", "", "", "") trace s
        where
                p   = 0
                len = read ret

ps_brk s args ret trace = pp_error $ text "unsupported argument:" <+> pp (trace,s)

ps_munmap :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_munmap s [addr, length] ret trace =
        let p   = read addr   :: Integer
            len = read length :: Integer
        in
                ps_delete_vma (p,len) trace s

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

                s'  = ps_update_vma (p,len) prot trace s


is_exec :: Strace  -> Bool
is_exec strace = strace_syscall strace =~ "^exec"
-- vm not shared
is_clone_process :: Strace -> Bool
is_clone_process  strace = strace_syscall strace =~ "^clone" &&
                           not (any (=~ "CLONE_VM") (strace_args strace))
-- vm shared
is_clone_thread :: Strace -> Bool
is_clone_thread   strace = strace_syscall strace =~ "^clone" &&
                           any (=~ "CLONE_VM") (strace_args strace)

pt_exec :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_exec tid s args ret (n,strace) =
        with_invariant "pt_exec" precondition postcondition s'
        where
                precondition    = pt_member tid s && tid == strace_tid strace && ret == "0"
                postcondition s = pt_member tid s && ps_null_vma (s .! tid)

                s' = pt_adjust (const $ ps_empty tid (n, strace)) tid s


pt_clone_thread :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_clone_thread tid s args ret strace =
        with_invariant "pt_clone_thread" precondition postcondition s'
        where
                precondition    = pt_member tid  s && not (pt_member tid' s) && tid' /= (-1)
                postcondition s = pt_member tid' s &&
                                  not (ps_null_vma (s .! tid')) &&
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
                                  not (ps_null_vma (s .! child_pid))  &&
                                  (s .! tid) == (s .! child_pid)

                child_pid  = read ret :: Pid
                parent_pid = ps_pid (s .! tid )
                s'         = pt_insert_process child_pid parent_pid s




{-
************************************************************************
*                                                                      *
*        5. Sheaves
*                                                                      *
************************************************************************

 Note that open == semidecidable, clopen == decidable

 @FIXME: 1. For now only the trivial fibration is implemented.
         2.

 Any first order theory should work, not just monads.
 The goal is to unify and generalize Maps, Sets, IntervalMaps, etc.,etc..
 Examples include the time series of Sets/Maps, Maps over computable sets, and
 of cource "the time series of trees of virtual address spaces" as in our example program.
 With sheaves it should even be possible to model processes with shared memory,
 processes on NUMA systems, distributed systems, or anything you can even (computably) dream of.
 Sheaves also generalize monads, but probably not in Haskelly way.

 Reference: Sheaves in Geometry and Logic, S.MacLane, I.Moerdijk

For utmost concreteness we will progressively advance from the simplest to the more complex.

First, set A = Q[dx,1/dx] (fixing some infinitesimal dx).
A is a hyper-real ring and is totally ordered.
It's not local, as each ideal (dx-a) == (1/dx-1/a) for which a/=0 is maximal.

Our first category OA:

objects  : *finite* unions of open intervals in A, including the empty set.
morphisms: inclusion as sets.

The fibered product A * B over X (i.e. the pullback of (A -> X <- B))
is the intersection A /\ B, which is also an object in OA.

Note that it's not complete nor cocomplete, and it's not topology in
ordinary sense.

Define a covering family of X to be a finite collection {X_i} of objects for which \/{X_i} == X.

This forms a Grothendieck pretopology. For, we have:
1. Fibered products exist.
2. Stability: Y -> X and X == \/{X_i} implies Y == \/{Y /\ X_i}.
3. Locality: X == \/{X_i} and X_i == \/{X_i_j} then X == \/{X_i_j}.
4. Isomorphisms: X == Y is a covering family.

The point is, we are freed from the insane uncomputablity of
ordinary topology! Now everything can be described by finite data
without losing any rigor. Thanks Grothendieck!

Now the sheaves. Fix some value-type V.

A sheaf F on OA is a contravariant functor OA^op -> V such that
for each covering family \/X_i == X, the diagram
F(X) -> ΠF(X_i) => ΠF(X_i /\ X_j)
of restictions is an equalizer.
Let's be concrete.

Let X   = X1 \/ X2
    X12 = X1 /\ X2 = X21
    0   = empty

    0                 |                 F(0)
    |      inclusion  | restriction      |
   X12       |        |     ^           F(X12)
    /\       |        |     |            /   \
  X1  X2     v        |     |         F(X1)  F(X2)
    \/                |                 \     /
    X                 |                  F(X)

If V were a set with equality,

r1 :: F(X) -> F(X1)
r1 = F(X1 -> X)

r2 :: F(X) -> F(X2)
r2 = F(X2 -> X)

r12 :: F(X1) -> F(X12)
r12 = F(X12 -> X1)

r21 :: F(X2) -> F(X21)
r21 = F(X21 -> X2)

f :: F(X) -> (F(X1),F(X2))
f x = (r1 x, r2 x)

f1 :: (F(X1),F(X2)) ->  (F(X1), F(X12), F(X21), F(X2))
f1 (x,y) = (x, r12 x, r21 y, y)

f2 :: (F(X1),F(X2)) ->  (F(X1), F(X12), F(X21), F(X2))
f2 (x,y) = (x, r21 y, r12 x, y)

(f1 . f) x == (r1 x, r12 (r1 x), r21 (r2 x), r2 x)
(f2 . f) x == (r1 x, r21 (r2 x), r12 (r1 x), r2 x)

So for all x.(r12 . r1) x == (r21 . r2) x, together with some unique F(0) == 1,
is necessary for it to be a sheaf. Because of finiteness of our category, that this
holds for any binary cover X==X1\/X2 can be proven sufficient by induction.

The category COA:
objects:   finite unions of half-open intervals [a,b)
morphisms: set inclusion

Let P be the power series functor PX = 1 + X + X^2 + X^3..
and let A* = PA.

-}

type Basis = HyperOpenInterval

data Section v = Section
                 { section_data     :: IntervalMap Basis v
                 }
               deriving (Show)

section_glue :: (Eq v, Default v) => Section v -> Section v -> Maybe (Section v)
section_glue (Section section) (Section section) = undefined

section_restrict :: (Eq v, Default v) => Section v -> Section v -> Section v
section_restrict (Section section) (Section section) = undefined



-- |Algebra of sections of sheaves, nullary operation. O(n)
-- Set the values on each open interval k to be (f k).
lift_section0 :: v -> Section v -> Section v
lift_section0 v a = with_invariant "lift_sheaf0"
                     precondition
                     postcondition
                     $ IntervalMap.map f a
        where
                precondition     = all disjoint_interval_tree [a] -- @FIXME: sheaf_valid
                postcondition vm = disjoint_interval_tree vm      -- @FIXME: sheaf_valid

-- | Unary operation.
lift_section1 :: (v -> v) -> Section v -> Section v
lift_section1 f a  = with_invariant "lift_sheaf1"
                   precondition
                   postcondition
                   $ IntervalMap.map f a
        where
                precondition     = all disjoint_interval_tree [a] -- @FIXME: coherency
                postcondition vm = disjoint_interval_tree vm      -- @FIXME: coherency


-- | O(n*m)
lift_sheaf2 :: (v -> v -> v) -> IntervalMap k v -> IntervalMap k v -> IntervalMap k v
lift_sheaf2 (*) a b = with_invariant "lift_sheaf2"
                      precondition
                      postcondition
                      $ union $ map (intersect a) (IntervalMap.toList b) -- @FIXME: slow
        where
                precondition      = all disjoint_interval_tree [a,b]
                postcondition vm  = disjoint_interval_tree vm

                intersect a (k,v) = let (lower, intersecting, upper) = IntervalMap.splitIntersecting a k
                                    in  intersect_slow intersecting (k,v)

                intersect_slow a (k,v) = let as = IntervalMap.toList a
                                         in  [ intersect_each (l,u) (k,v) | (l,u) <- as ]

                intersect_each (l,u) (k,v) =
                        case colim [l, k] of
                        Just lk -> (lk, u*v)
                        Nothing -> error "impossible"

                union xss = IntervalMap.fromList $ concat xss



{-
************************************************************************
*                                                                      *
*        6. A (local) ring of hyperreals generated by (1,dx,1/dx)
*                                                                      *
************************************************************************
-}

data Hyper a = Hyper { hyper_inv_dx :: [a] -- Infinites
                     , hyper_std    :: a   -- Standard part
                     , hyper_dx     :: [a] -- Infinitesimals
                     }
              deriving(Eq,Show)
type HyperMonomial a = (a, Integer)

hyper_d :: Hyper a -> Hyper a
hyper_d (Hyper is x es) = Hyper [] 0 es

hyper_inf :: Hyper a -> Hyper a
hyper_inf (Hyper is x es) = Hyper is 0 []


hyper_degree :: Hyper a -> Integer
hyper_degree (Hyper is x es) =
        let is_rev = dropWhile (==0) $ reverse is
            es_rev = dropWhile (==0) $ reverse es
        in
                case (null is_rev, x == 0, null es_rev) of
                (False, _, _)         -> length is_rev
                (True , False, _)     -> 0
                (True , True , False) -> length es_rev
                (True , True , True)  -> 0


hyper_monomial_mult (coeff, deg) (coeff', deg') = (coeff*coeff', deg + deg')
hyper_from_monomials ms = foldl' 0 (+) (map hyper_from_monomial ms)
hyper_from_monomial (coeff, deg)
        | deg >  0  = Hyper (reverse (coeff : zeros (deg -1))) 0 []
        | deg == 0  = coeff
        | deg <  0  = Hyper [] 0 (reverse (coeff : zeros (-deg-1)))
        where
                zeros n = take n $ repeat 0

hyper_monomials :: Hyper a -> [HyperMonomial a]
hyper_monomials (Hyper is x es) = zip is [1,2..] ++ [(x,0)] ++ zip es [-1,-2..]

hyper_mult h h'  = let ms  = hyper_monomials h
                       ms' = hyper_monomials h'
                   in hyper_from_monomials $ [hyper_monomial_mult m m' | m <- ms , m' <- ms' ]

hyper_add h h'   =
        let Hyper is  x  es  = h
            Hyper is' x' es' = h'
        in
                hyper_canonicalize $ Hyper (list_add is is') (x+x') (list_add es es')



instance Functor Hyper where
        fmap f (Hyper i x e) = Hyper (f i) (f x) (f e)

instance Ord (Hyper a) where
        h > h' = hyper_leading_coefficient (h - h') > 0

instance Num a => Num (Hyper a) where
        (*) = hyper_mult
        (+) = hyper_add
        negate (Hyper is x es)  = Hyper (map negate is) (negate x) (map negate es)
        fromInteger x           = Hyper [] (fromInteger x) []
        abs h                   = if h > 0 then h else -h
        signum h                = if h > 0 then 1 else if h == 0 then 0 else -1

instance Bits a => Bits (Hyper a) where
        h `shiftL` n = hyper_canonicalize $ fmap (`shiftL` n) h
        h `shiftR` n = hyper_canonicalize $ fmap (`shiftR` n) h
        (.&.) = undefined
        (.|.) = undefined
        complement = undefined
        rotate = undefined
        bitSize = undefined
        bitSizeMaybe = undefined
        isSigned = undefined
        testBit = undefined
        bit = undefined
        popCount = undefined
        xor = undefined



-- Special constants representing the unit positive infinite/infinitesimal
dx :: Num a => Hyper a
dx = Hyper [] 0 [1]

inf :: Num a => Hyper a
inf = Hyper [1] 0 []

hyper_leading_coefficient :: Hyper a -> a
hyper_leading_coefficient (Hyper is x es)
        | not (null is) = last_non_zero is
        | x /= 0        = x
        | not (null es) = first_non_zero es
        | otherwise     = 0

hyper_canonicalize :: Hyper a -> Hyper a
hyper_canonicalize (Hyper is x es) = Hyper is' x es'
        where
                is' = strip_right_if (==0) is
                es' = strip_right_if (==0) es

strip_right_if p  = reverse . dropWhile p . reverse
first_non_zero    = head . dropWhile (==0)
last_non_zero     = first_non_zero . reverse

list_add xs ys
        | length xs > length ys = zipWith(+) xs (ys ++ repeat 0)
        | otherwise             = zipWith(+) (xs ++ repeat 0) ys

hyper_inj :: a -> Hyper a
hyper_inj = fromIntegral

--
--      Hyper interval arithmetics
--      Sufficient to deal only with the open intervals (which is the whole point)
--

type HyperOpenInterval = (Hyper Integer, Hyper Integer)

-- | The open interval (x,x) is empty
hyper_interval_null :: Ord a => (Hyper a, Hyper a) -> Bool
hyper_interval_null (a,b) = a >= b

hyper_interval_intersection :: HyperOpenInterval -> HyperOpenInterval -> [HyperOpenInterval]
hyper_interval_intersection i@(ix,iy) j@(jx,jy) =
        with_invariant "hyper_interval_intersection" precondition postcondition
        $ f (max ix jx, min iy jy)
        where
                precondition  = True -- always works
                postcondition = all valid

                valid = not . hyper_interval_null

                f i | valid i   = [i]
                    | otherwise = []

hyper_interval_disjoint = null . hyper_interval_intersection

hyper_interval_union :: HyperOpenInterval -> HyperOpenInterval -> [HyperOpenInterval]
hyper_interval_union i@(ix,iy) j@(jx,jy)
        | hyper_interval_disjoint i j = filter (not . hyper_interval_null) [i,j]
        | otherwise                   = [(min ix jx, max iy jy)]


--
-- Standard interval arithmetics
--

interval_null = Interval.isEmpty

interval_intersection :: Interval -> Interval -> [Interval]
interval_intersection iv jv = map $ from_hyper $ hyper iv /\ hyper jv
        where (/\) = hyper_interval_intersection


interval_complement :: Interval -> [HyperOpenInterval]
interval_complement i = let (a,b) = hyper i
                        in  [(-inf,  a-dx) , (b+dx, inf)]

interval_diff :: Interval -> Interval -> [HyperOpenInterval]
interval_diff iv jv = let [i1,i2] = interval_complement iv
                          j       = hyper jv
                    in  (i1 /\ j) \/ (i2 /\ j)
        where
                (/\) = hyper_interval_intersection
                (\/) = (++)

hyper :: Interval -> HyperOpenInterval
hyper iv = case iv of
        (IntervalMap.IntervalCO     x y) -> (i x - dx, i y)
        (IntervalMap.ClosedInterval x y) -> (i x - dx, i y + dx)
        (IntervalMap.OpenInterval   x y) -> (i x, i y)
        (IntervalMap.IntervalOC     x y) -> (i x, i y + dx)
        where
                i = fromIntegral

from_hyper :: HyperOpenInterval -> Interval
from_hyper (a,b) =
        with_invariant "from_hyper"
        precondition
        postcondition
        $ iv
        where
                precondition    = hyper_degree a <= 0 &&
                                  hyper_degree b <= 0 &&
                                  da <= 0 && db >= 0

                postcondition iv = Interval.lowerBound iv == sa &&
                                   Interval.upperBound iv == sb

                iv | da <  0 && 0 <  db = IntervalMap.ClosedInterval sa sb
                   | da <  0 && 0 == db = IntervalMap.IntervalCO     sa sb
                   | da == 0 && 0 <  db = IntervalMap.IntervalOC     sa sb
                   | da == 0 && 0 == db = IntervalMap.OpenInterval   sa sb

                da = hyper_d a
                db = hyper_d b

                sa = hyper_std a
                sb = hyper_std b


-- |Set difference
vm_diff :: VMATree -> VMATree -> VMATree
vm_diff = lift_sheaf2_ f
        where
                f x y = Nothing


{-
************************************************************************
*                                                                      *
*              6. Utilities
*                                                                      *
************************************************************************
-}

chomp            = strip_left . strip_right
strip_right_if p = reverse . strip_left_if p . reverse
strip_left_if  p = dropWhile p
strip_right = strip_right_if isSpace
strip_left  = strip_left_if  isSpace


map_keys   = map fst . Map.toList
map_values = map snd . Map.toList
map_adjust f k m = with_invariant "map_adjust" (Map.member k m) (Map.member k) $ Map.adjust f k m

imap_keys   = map fst . IntervalMap.toList
imap_values = map snd . IntervalMap.toList
(\/) :: VMATree -> VMATree -> VMATree
a \/ b = IntervalMap.union a b



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


trace :: Show a => a -> a
trace x = unsafePerformIO $ do
        print x
        return x

assert' desc p x | p x = x
                 | otherwise = error $ "assertion failed:" ++ desc

test' desc p x | p x = True
               | otherwise = error $ "test failed:" ++ desc


-- |@tbd switch it off with -DNDEBUG
--  Careful with the evaluation order
with_invariant :: Show a => String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret = ret'
        where
                ret' =  assert' (":precondition:"  ++ desc) (const pre) $
                        assert' (":postcondition:" ++ desc) post        $
                        ret



{-
************************************************************************
*                                                                      *
*              7. Testing and debugging
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
*              8. IO
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
                summarize = assert' "disjoint" (all pt_disjoint) . snapshot 1000


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
