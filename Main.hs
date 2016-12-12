{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
************************************************************************
*                                                                      *
*              A Linux 64-bit VM emulator
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

Note:
1. All the functions are in underscore_case to distinguish them from
   the library functions,
2. Uses Strings exclusively, since bottleneck is elsewhere. Feel free to improve it ;)
3. Should be like two orders of magnitudes faster
-}

module Main    where

import Numeric
import Pretty
import Invariant
import Hyper
import Sheaf
import PrettySheaf()

import Data.Maybe
import Data.List
import Data.List.Split
import Data.Char
import Data.Hashable
import Data.Bits

import Data.Map (Map,(!))
import qualified Data.Map as Map

import Text.Regex
import Text.Regex.PCRE

import           Text.Parsec ((<|>))
import qualified Text.Parsec as Parsec

import GHC.Generics (Generic)
import Control.DeepSeq
import Control.Exception

import System.Environment
import System.Exit
import System.IO
import System.IO.Unsafe -- for our in-house hacky streaming IO

{-
************************************************************************
*                                                                      *
*              1. Strace parser objects
*                                                                      *
************************************************************************
-}


data Strace =
        Strace
        { strace_tid     :: Integer
        , strace_syscall :: String
        , strace_args    :: SyscallArgs
        , strace_ret     :: SyscallRet
        , strace_stack   :: [StraceLine]
        }
        | StraceError
        { strace_tid     :: Integer
        , strace_syscall :: String
        , strace_args    :: SyscallArgs
        , strace_ret     :: SyscallRet
        , strace_err     :: String
        , strace_stack   :: [StraceLine]
        }
        | StraceExit
          { strace_tid       :: Integer
          , strace_exit_code :: Integer
          , strace_stack     :: [StraceLine]
          }
        | StraceSignal
          { strace_tid     :: Integer
          , strace_signal  :: String
          , strace_args    :: SyscallArgs
          }

        deriving (Eq,Show, Generic, NFData)


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
          deriving (Eq,Show, Generic, NFData)

-- might use RecordWildCards..
is_syscall :: StraceLine -> Bool
is_syscall (Syscall _ _ _ _) = True
is_syscall _ = False

is_syscall_error :: StraceLine -> Bool
is_syscall_error (SyscallError _ _ _ _ _) = True
is_syscall_error _ = False

is_syscall_unfinished :: StraceLine -> Bool
is_syscall_unfinished (SyscallUnfinished _ _ _) = True
is_syscall_unfinished _ = False

is_syscall_resumed :: StraceLine -> Bool
is_syscall_resumed (SyscallResumed _ _ _ _) = True
is_syscall_resumed _ = False

is_syscall_resumed_error :: StraceLine -> Bool
is_syscall_resumed_error (SyscallResumedError _ _ _ _ _) = True
is_syscall_resumed_error _ = False

is_stack_trace :: StraceLine -> Bool
is_stack_trace (StackTrace _) = True
is_stack_trace _ = False

is_exit :: StraceLine -> Bool
is_exit (Exit _ _) = True
is_exit _ = False

is_signal :: StraceLine -> Bool
is_signal (Signal _ _ _) = True
is_signal _ = False



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
        let matches = x  =~ "^(\\d+) +(\\w+) *\\((.*)\\) *= *([\\S]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args, ret]] -> Just (tid, syscall, args, ret)
                _                              -> Nothing

-- 18233 mlockall(MCL_CURRENT)             = -1 ENOMEM (Cannot allocate memory)
parse_syscall_entry_error :: String -> Maybe (String, String, String, String, String)
parse_syscall_entry_error x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^)]*)\\) *= *([\\S]+) +(\\w.*)$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args, ret, err]] -> Just (tid, syscall, args, ret, err)
                _                                   -> Nothing


-- 18253 mmap(0x7f390ac62000, 12288, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS, -1, 0 <unfinished ...>
parse_syscall_unfinished :: String -> Maybe (String, String, String)
parse_syscall_unfinished x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^<]*) *< *unfinished *\\.\\.\\.> *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args]] -> Just (tid, syscall, args)
                _                         -> Nothing

-- 18253 <... mmap resumed> )              = 0x7f390ac62000
parse_syscall_resumed :: String -> Maybe (String, String, String, String)
parse_syscall_resumed x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *(.*) *\\) *= *([^()=\\s]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, arg_rest, ret]] -> Just (tid, syscall, arg_rest, ret)
                _                                  -> Nothing

-- 18253 <... mmap resumed> )              = -1 ENOMEM.*
parse_syscall_resumed_error :: String -> Maybe (String, String, String, String, String)
parse_syscall_resumed_error x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *(.*) *\\) *= *([^=\\s]+) +([^=]+)$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args_rest, ret, err]] -> Just (tid, syscall, args_rest, ret, err)
                _                                        -> Nothing


--  > /lib/x86_64-linux-gnu/ld-2.19.so(realloc+0x3dc) [0x1814c]
parse_stack_trace :: String -> Maybe String
parse_stack_trace x =
        let matches = x  =~ "^ *> *(.*) *$" :: [[String]]
        in
                case matches of
                [[_, trace_line]] -> Just trace_line
                _                 -> Nothing

-- 18232 +++ exited with 130 +++
parse_exit :: String -> Maybe (String, String)
parse_exit x = let matches = x  =~ "^ *(\\d+) +\\+\\+\\+ *exited +with +(\\d+) +\\+\\+\\+ *$" :: [[String]]
               in
                       case matches of
                       [[_, tid, status]] -> Just (tid, status)
                       _                  -> Nothing

-- 18239 --- SIGSEGV {si_signo=SIGSEGV, si_code=SEGV_ACCERR, si_addr=0x7f3927f28b80} ---
parse_signal :: String -> Maybe (String, String, String)
parse_signal x = let matches = x  =~ "^ *(\\d+) *--- *(\\w+) *{(.*)} *--- *$" :: [[String]]
               in
                       case matches of
                       [[_, tid, sig, args]] -> Just (tid, sig, args)
                       _                     -> Nothing


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
                        = Syscall (i tid) syscall (split_args args) ret
                syscall_entry_error (tid, syscall, args, ret, err)
                        = SyscallError (i tid) syscall (split_args args) ret err
                syscall_unfinished  (tid, syscall, args)
                        = SyscallUnfinished (i tid) syscall (split_args args)
                syscall_resumed     (tid, syscall, args_rest, ret)
                        = SyscallResumed (i tid) syscall (split_args args_rest) ret
                syscall_resumed_error (tid, syscall, args_rest, ret, err)
                        = SyscallResumedError (i tid) syscall (split_args args_rest) ret err
                stack_trace trace_line
                        = StackTrace trace_line
                exit (tid, status)
                        = Exit (i tid) (i status)
                signal (tid, sig, args)
                        = Signal (i tid) sig (split_args args)
                i = read

                split_args ""  = []
                split_args cs  = map chomp $ splitOn "," cs


-- |Parse whole strace output string
parse :: String -> [StraceLine]
parse s = map parse_line (lines s)



-- |Id is used to identify stack straces
strace_with_id :: [StraceLine] -> [(Id,Strace)]
strace_with_id = zip [1..] . strace

-- lazy parser
type StraceState = Map Tid StraceLine

ss_empty = Map.empty :: StraceState

type StraceStream    = [StraceLine]
type ParseStrace     = Parsec.Parsec StraceStream StraceState
type ParseStraceCont = ParseStrace (Maybe Strace, StraceStream, StraceState)

strace :: [StraceLine] -> [Strace]
strace xs = catMaybes $
            map result $
            takeWhile (not . eof) $
            iterate strace1 (Right (Nothing, xs, ss_empty))
        where
                result (Right (a, _, _)) = a
                result (Left err)        = error $ show err

                eof (Right (Nothing, [], _)) = True
                eof _ = False

strace1 :: Either Parsec.ParseError (Maybe Strace, StraceStream, StraceState)
        -> Either Parsec.ParseError (Maybe Strace, StraceStream, StraceState)
strace1 (Left err) = Left err
strace1 (Right (_, xs, st)) =  Parsec.runParser (parse_strace1 <|> eof) st "source" xs
        where
                eof = do Parsec.eof
                         parser_return Nothing

-- tokens

instance Pretty Parsec.SourcePos where pp_level _ = text . show

just_if p x | p x = Just x
            | otherwise = Nothing

show_tok = render . pp
test_tok p = just_if p

pos_tok :: Parsec.SourcePos -> StraceLine -> StraceStream -> Parsec.SourcePos
pos_tok pos x xs = Parsec.incSourceLine pos 1

define_token :: (StraceLine -> Bool) -> ParseStrace StraceLine
define_token p = Parsec.tokenPrim show_tok pos_tok (test_tok p)

token_syscall :: ParseStrace StraceLine
token_syscall = define_token is_syscall

token_syscall_error :: ParseStrace StraceLine
token_syscall_error = define_token is_syscall_error

token_syscall_unfinished :: ParseStrace StraceLine
token_syscall_unfinished = define_token is_syscall_unfinished

token_syscall_resumed :: ParseStrace StraceLine
token_syscall_resumed = define_token is_syscall_resumed

token_syscall_resumed_error :: ParseStrace StraceLine
token_syscall_resumed_error = define_token is_syscall_resumed_error

token_trace :: ParseStrace StraceLine
token_trace = define_token is_stack_trace

token_exit :: ParseStrace StraceLine
token_exit = define_token is_exit

token_signal :: ParseStrace StraceLine
token_signal = define_token is_signal


parse_strace1 :: ParseStraceCont
parse_strace1 = parse_strace_syscall <|>
                parse_strace_syscall_error <|>
                parse_strace_syscall_unfinished <|>
                parse_strace_syscall_resumed <|>
                parse_strace_syscall_resumed_error <|>
                parse_strace_exit <|>
                parse_strace_signal

parser_return :: Maybe Strace -> ParseStraceCont
parser_return x = do
        input <- Parsec.getInput
        st    <- Parsec.getState
        return (x, input, st)

assertM p = assert p $ return ()

push_unfinished :: StraceLine -> ParseStrace ()
push_unfinished l@(SyscallUnfinished tid syscall args) = do
        st <- Parsec.getState
        assertM (not $ Map.member tid st)
        Parsec.putState $ Map.insert tid l st

pop_unfinished :: Tid -> ParseStrace StraceLine
pop_unfinished tid = do
        st <- Parsec.getState
        assertM (Map.member tid st)
        return $ st ! tid


parse_strace_syscall :: ParseStraceCont
parse_strace_syscall = do
        Syscall tid syscall args ret <- token_syscall
        t <- parse_strace_trace
        parser_return $ Just $ Strace tid syscall args ret t


parse_strace_syscall_error :: ParseStraceCont
parse_strace_syscall_error = do
        SyscallError tid syscall args ret err <- token_syscall_error
        t <- parse_strace_trace
        parser_return $ Just $ StraceError tid syscall args ret err t


parse_strace_syscall_unfinished :: ParseStraceCont
parse_strace_syscall_unfinished = do
        l@(SyscallUnfinished tid syscall args) <- token_syscall_unfinished
        push_unfinished l
        parser_return $ Nothing

parse_strace_syscall_resumed :: ParseStraceCont
parse_strace_syscall_resumed = do
        SyscallResumed tid syscall args ret   <- token_syscall_resumed
        t                                     <- parse_strace_trace
        SyscallUnfinished tid' syscall' args' <- pop_unfinished tid
        assertM (tid == tid' && syscall == syscall')
        parser_return $ Just $ Strace tid syscall (args' ++ args) ret t


parse_strace_syscall_resumed_error :: ParseStraceCont
parse_strace_syscall_resumed_error = do
        SyscallResumedError tid syscall args ret err <- token_syscall_resumed_error
        t                                            <- parse_strace_trace
        SyscallUnfinished tid' syscall' args'        <- pop_unfinished tid
        assertM (tid == tid' && syscall == syscall')
        parser_return $ Just $ StraceError tid syscall (args' ++ args) ret err t

parse_strace_exit :: ParseStraceCont
parse_strace_exit = do
        Exit tid status   <- token_exit
        t                                     <- parse_strace_trace
        parser_return $ Just $ StraceExit tid status t

parse_strace_signal :: ParseStraceCont
parse_strace_signal = do
        Signal tid signal args   <- token_signal
        parser_return $ Just $ StraceSignal tid signal args


parse_strace_trace :: ParseStrace [StraceLine]
parse_strace_trace = Parsec.many token_trace




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
strace_is_exec (Strace _ syscall _ _ _) = syscall =~ "^exec"
strace_is_exec _  = False

-- vm not shared
strace_is_clone_process :: Strace -> Bool
strace_is_clone_process  strace@(Strace _ _ _ _ _) =
        strace_syscall strace =~ "^clone" &&
        not (any (=~ "CLONE_VM") (strace_args strace))
strace_is_clone_process _ = False

-- vm shared
strace_is_clone_thread :: Strace -> Bool
strace_is_clone_thread   strace@(Strace _ _ _ _ _) =
        strace_syscall strace =~ "^clone" &&
        any (=~ "CLONE_VM") (strace_args strace)
strace_is_clone_thread _ = False

strace_is_wait :: Strace -> Bool
strace_is_wait strace@(Strace _ _ _ _ _) =
        strace_syscall strace =~ "^wait"
strace_is_wait _ = False

strace_is_exit :: Strace -> Bool
strace_is_exit (StraceExit _ _ _) = True
strace_is_exit _ = False

strace_is_error :: Strace -> Bool
strace_is_error (StraceError _ _ _ _ _ _) = True
strace_is_error _ = False

strace_is_signal :: Strace -> Bool
strace_is_signal (StraceSignal _ _ _) = True
strace_is_signal _ = False



{-
************************************************************************
*                                                                      *
*              3. Pretty printers
*                                                                      *
************************************************************************
-}

instance Pretty StraceLine    where pp_level n = text . show
instance Pretty Strace        where pp_level n = pp_strace_level n
instance Pretty ProcessState  where
        pp_level n  (PState vm strace pid) =
                pp_data "PState"
                [ ("pid"   , integer    pid)
                , ("strace", pp_level n strace)
                , ("vm"    , pp_level n vm)
                ]

instance Pretty VMAInfo       where
        pp_level n (VMAInfo prot flags fd offs advise sync trace) =
                pp_data "VMAInfo"
                [ ("prot"  , text prot)
                , ("flags" , text flags)
                , ("fd"    , text fd)
                , ("offset", text offs)
                , ("advice", text advise)
                , ("sync"  , text sync)
                , ("trace" , pp_level n trace)
                ]


instance Pretty ProcessTreeState where
        pp_level n (PTState psmap tidmap refmap timestamp) =
                pp_data "PTState"
                [ ("ps"  , pp_level n psmap)
                , ("tid" , pp_level n tidmap)
                , ("ref" , pp_level n refmap)
                , ("timestamp", pp_timestamp timestamp)
                ]



data IntervalRelation  = Region :~: ProcessState
                       deriving (Show)

instance Pretty IntervalRelation where
        pp_level n  (iv :~: s) = pp iv <+> text "len=" <> pp area <+> text ":~: s =" $$  pp_level n rel
                where
                        rel   = section_translate (-x) $ (ps_vm s)
                        (x,y) = from_gen iv :: (Hyper Integer, Hyper Integer)
                        area  = gen_area iv

pp_strace_line :: StraceLine -> Doc
pp_strace_line l = text (show l)


pp_strace = pp_strace_level inf

pp_strace_level :: Hyper Integer -> Strace -> Doc
pp_strace_level n (Strace tid syscall args ret trace) =
        integer tid <+> text syscall <> pp_args args <+> text "=" <+> text ret $$
        vcat_level n (map (text . sl_call_stack) trace)

pp_strace_level n (StraceError tid syscall args ret err trace) =
        integer tid <+> text syscall <> pp_args args <+> text "=" <+> text ret <+> text err $$
        vcat_level n (map (text . sl_call_stack) trace)

pp_strace_level n (StraceExit tid code trace) =
         integer tid <+> text "exit"  <+> equals <+> integer code $$
         vcat_level n (map (text . sl_call_stack) trace)

pp_strace_level n (StraceSignal tid signal args) =
        integer tid <+> text "signal"  <+> equals <+> text signal <+> pp_args args


pp_data_frame_header = text "t pid from to v trace_id"

pp_data_frame :: [PTState] -> Doc
pp_data_frame ss = pp_data_frame_header $$ body
        where
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


-- R has a nasty bug in read.table that prevents reading the sequence \\\" correctly
escape_fix_regex = mkRegex $ bs ++ bs ++ bs ++ dq
        where
                bs = "\\"
                dq = "\""

escape :: Doc -> Doc
escape s    = text $ bugfix $ show $ render_left s
        where
                bugfix :: String -> String
                bugfix s = subRegex escape_fix_regex s "''"

{- | The fields are as follows:
1. trace_id:     The unique ID of the trace
2. t:            The time of the trace
3. pid:          The pid that the tid belongs to
4. tid:          The tid of the trace
5. success:      1:Success 0:Error
6. child_pid:    the child pid if cloning a process, or 0 otherwise
7. syscall:      1:exec* 2:clone_process  0:others
7. trace:        The escaped string of the stack trace
-}
pp_trace_header :: Doc
pp_trace_header = text "trace_id t pid tid success child_pid syscall trace"

data TraceDataFrame = TD
                      { td_trace_id :: Int
                      , td_t        :: Timestamp
                      , td_tid      :: Tid
                      , td_success  :: Bool
                      , td_syscall  :: Strace
                      }
                      deriving (Eq,Show)

pp_trace_generic :: PTState -> TraceDataFrame -> Doc
pp_trace_generic pt (TD trace_id t tid success strace) =
        pp trace_id <+> pp t <+> pp pid <+> pp tid <+> success' <+> child_pid <+> syscall <+> trace
        where
                pid = pt_pid tid pt
                success' | success   = int 1
                         | otherwise = int 0

                trace = escape (pp t <+> pp strace)

                child_pid | strace_is_clone_process strace = integer $ read $ strace_ret strace
                          | otherwise                      = int 0

                syscall = pp $ syscall_code strace

syscall_code :: Strace -> Int
syscall_code trace | strace_is_exec   trace =  1
                      | strace_is_clone_process trace = 2
                      | strace_is_exit   trace = 3
                      | strace_is_signal trace = 4
                      | otherwise            =  0

pp_trace ::  (PTState, UniqueStrace) -> Doc
pp_trace (pt, (n, t)) | not (pt_member (strace_tid t) pt) =
                        pp_error $ text "pp_trace" $$ pp (pp t, pp_brief pt)

-- Just use time=n for the moment
pp_trace (pt, (n, t@(Strace tid syscall args ret trace))) =
        pp_trace_generic pt (TD n time tid True t)
        where time = fromIntegral n

pp_trace (pt, (n, t@(StraceError tid syscall args ret err trace))) =
        pp_trace_generic pt (TD n time tid False t)
        where time = fromIntegral n

pp_trace (pt, (n, t@(StraceExit tid code trace))) =
        pp_trace_generic pt (TD n time tid True t)
        where time = fromIntegral n

pp_trace (pt, (n, t@(StraceSignal tid signal args))) =
        pp_trace_generic pt (TD n time tid True t)
        where time = fromIntegral n


pp_args :: [String] -> Doc
pp_args xs = pp_tuple $ map text xs


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
               , vma_advice :: String  -- ^ madvice args
               , vma_sync   :: String  -- ^ msync flags
               , vma_trace  :: Maybe UniqueStrace
               }
            deriving (Eq,Show, Generic, NFData)

instance Hashable VMAInfo where
        hashWithSalt n (VMAInfo a b c d e f _) = hashWithSalt n (a,b,c,d,e,f)

-- Any address can be made accessible by mprotect
vm_info_default  = VMAInfo "" "" "" "" "" "" Nothing :: VMAInfo

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
             deriving (Eq,Show, Generic, NFData)

type PState  = ProcessState

ps_valid :: PState -> Bool
ps_valid (PState vm st pid) = section_valid vm && pid > 0

ps_empty :: Pid -> UniqueStrace -> PState
ps_empty pid strace = PState section_empty strace pid

ps_null_vm :: PState -> Bool
ps_null_vm s = section_null $ ps_vm s

ps_intersects :: Region -> PState -> Bool
ps_intersects region s = not $ section_null $ section_components_at region (ps_vm s)

-- | Does the address space densely cover g with no rational points left out?
ps_contained_in :: Region -> PState -> Bool
ps_contained_in g s  = area (g'/\s') == area g' &&
                       a /= std a &&
                       b /= std b
        where
                x /\ y = section_lift2 const x y
                area   = section_area
                g'     = section_singleton (g, ())
                s'     = ps_vm s
                (a,b)  = from_gen g
                std    = fromIntegral . hyper_std

type Timestamp = Integer

data RoseTree a = RoseTree a [RoseTree a]
                deriving (Eq,Show, Generic, NFData)

-- @tbd The whole state can and should be sheafified too
data ProcessTreeState = PTState
                        { pt_ps_map    :: Map Pid ProcessState
                        , pt_tid_map   :: Map Tid Pid
                        , pt_pid_ref   :: Map Pid Integer
                        , pt_timestamp :: Timestamp
                          -- @tbd
                          -- , ptree_tree :: RoseTree Pid
                        }
                      deriving (Eq,Show, Generic, NFData)

type PTState = ProcessTreeState

pt_num_processes :: PTState -> Int
pt_num_processes pt = Map.size $ pt_ps_map pt

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
s .! tid = with_invariant (report "(.!)" (tid, pp_brief s))
           (Map.member tid (pt_tid_map s) && Map.member (pt_tid_map s ! tid) (pt_ps_map s))
           (const True)
           $ pt_ps_map s ! (pt_tid_map s ! tid)

pt_member :: Tid -> PTState -> Bool
pt_member tid (PTState ps_map tid_map ref_map stamp) =
        case Map.lookup tid tid_map of
        Just pid -> Map.member pid ps_map && Map.member pid ref_map
        Nothing  -> False

pt_pid :: Tid -> PTState -> Pid
pt_pid tid pt = ps_pid $ pt .! tid

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

zip_safe [] [] = []
zip_safe (x:xs) (y:ys) = (x,y):zip_safe xs ys

-- |Main VM emulator function
--  strace object is returned to annotate trace
-- A process state may not correspond to a tracable syscall
emulate_vm :: [UniqueStrace] -> [(PTState, Maybe UniqueStrace)]
emulate_vm syscalls =
        with_invariant (printf "emulate_vm:%s" (show $ take 10 syscalls))
        precondition
        postcondition
        $ zip_safe (s0:s) (map Just syscalls ++ [Nothing]) -- syscalls are not annotated currently

        where
                precondition     = not (null syscalls)
                postcondition ss = not (null ss)

                s0 = pt_singleton (head syscalls)
                s  = scanl (<*)  s0 (tail syscalls)

                s <*  (n,syscall) = let t = fromIntegral n -- @tbd: use genuine timestamp
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
                vmainfo = vm_info_default
                          { vma_prot  = prot
                          , vma_flags = flags
                          , vma_fd    = fd
                          , vma_offset = offset
                          , vma_trace  = Just trace
                          }

                g /\ s = section_lift2 const (ps_vm s) (section_singleton (g, ()))


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

                t =  ps_act_vm (restrict_to_compl g) s

                restrict_to_compl g vm = let s1 = head $ gen_compliments g
                                         in  vm /\ s1

                x /\ y = section_lift2 const x y

vm_diff :: VM -> VM -> VM
vm_diff x y =
        with_invariant "vm_diff"
        precondition
        postcondition
        x'
        where
                precondition = True
                postcondition x' = vm_area x' == vm_area x - vm_area xy

                x /\ y = section_lift2 const x  y
                c x    = head $ section_compliments x

                xy = x /\ y
                x' = x /\ c xy

vm_area = section_area

-- | Generic vma updater
--   vma info for unmapped region defaults to vm_info_default
ps_update_vma :: Region -> (VMAInfo -> VMAInfo) -> PState -> PState
ps_update_vma g update s =
        with_invariant (report "ps_update_vma" (ps_area t, vm_area (ps_vm t /\ g'), ps_area s))
        precondition
        postcondition
        t
        where
                precondition    = vma_valid g && ps_valid s
                postcondition t = vm_area t' == vm_area s' + vm_area (g'\\s')
                        where
                                t' = ps_vm t :: VM
                                s' = ps_vm s :: VM

                g'   = section_singleton (g, update vm_info_default)

                t  = let f vm = (g' \\ vm) \/ (vm /\ g') \/ (vm \\ g')
                     in  ps_act_vm f s

                x \\ y =  x `vm_diff` y
                x \/ y =  fromJust $ section_glue x y
                x /\ y =  section_lift2 (\x y -> update x) x y


-- |See mprotect(2)
ps_protect_vma :: Region -> String -> UniqueStrace -> PState -> PState
ps_protect_vma g prot trace s = ps_update_vma g update s
        where
                update vma = vma { vma_prot = prot
                                 , vma_trace = Just trace
                                 }

-- |See madvise(2)
ps_advise_vma :: Region -> String -> UniqueStrace -> PState -> PState
ps_advise_vma g ad trace s = ps_update_vma g update s
        where
                update vma = vma { vma_advice = ad
                                 , vma_trace  = Just trace
                                 }

-- |See msync(2)
ps_sync_vma :: Region -> String -> UniqueStrace -> PState -> PState
ps_sync_vma g flags trace s = ps_update_vma g update s
        where
                update vma = vma { vma_sync  = flags
                                 , vma_trace = Just trace
                                 }


-- |VMA state transition function for processes
-- Use sequence number to identify stack traces
ps_action :: PState -> UniqueStrace -> PState
ps_action s t@(n, Strace tid "mmap"     args ret trace) = ps_mmap     s args ret t
ps_action s t@(n, Strace tid "munmap"   args ret trace) = ps_munmap   s args ret t
ps_action s t@(n, Strace tid "mprotect" args ret trace) = ps_mprotect s args ret t
ps_action s t@(n, Strace tid "madvise"  args ret trace) = ps_madvise  s args ret t
ps_action s t@(n, Strace tid "msync"    args ret trace) = ps_msync    s args ret t
ps_action s t@(n, Strace tid "brk"      args ret trace) = ps_brk      s args ret t
ps_action s t = pp_error $ text "ps_action:unsupported syscall -- please improve this" $$
                pp t $$
                pp_summary s


-- |VMA state transition function for process trees
pt_action :: PTState -> UniqueStrace -> PTState
pt_action s (n, t@(Strace tid syscall args ret trace))
        | strace_is_exec t           = pt_exec          tid s args ret (n,t)
        | strace_is_clone_process t  = pt_clone_process tid s args ret (n,t)
        | strace_is_clone_thread  t  = pt_clone_thread  tid s args ret (n,t)
        | strace_syscall t == "vfork"      = pt_vfork   tid s args ret (n,t)
        | strace_syscall t == "exit"       = s -- exiting happens later
        | strace_syscall t == "exit_group" = s -- same
        | ignored_call t                   = s
        | otherwise                  = pt_act_vm (ps_action' (n,t)) tid s
        where
                ps_action' = flip ps_action
                ignored_call t = strace_syscall t =~ "^(wait|arch_prctl)" :: Bool

pt_action s (n, t@(StraceExit tid code trace)) =
        pt_exit tid s code (n,t)

-- skip
pt_action s (n, t@(StraceError tid syscall args ret err trace)) = s
pt_action s (n, t@(StraceSignal tid signal args)) = s




ps_mmap :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_mmap s [addr, length, prot, flags, fd, offset] ret trace =
        let p    = read ret    :: Integer
            len  = read length :: Integer
            anon = "MAP_ANON" `isInfixOf` flags  :: Bool
        in
                ps_insert_vma (region p len) (prot, flags, fd, offset) trace s

-- |Let's just assume the data segment starts at zero..
ps_brk :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_brk s [_] ret trace = ps_insert_vma (region base len) ("", "", "", "") trace s
        where
                addr = read ret :: Integer
                base = max 4096 (addr - len)
                len  = 30 * 2^20 -- heuristic


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
        with_invariant (report "ps_mprotect" (pp $ g :~: t, pp trace))
        precondition
        postcondition
        t
        where
                precondition    = read ret == 0 && strace_syscall (snd trace) == "mprotect"
                postcondition t = g `ps_contained_in` t

                p   = read addr   :: Integer
                len = read length :: Integer
                g   = region p len
                t   = ps_protect_vma g prot trace s

ps_mprotect s args ret trace = pp_error $ text "ps_mprotect:invalid argument" $$ pp_args args $$ pp trace

ps_madvise :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_madvise s [addr, length, ad] ret trace =
        with_invariant (report "ps_madvise" (pp $ g :~: t, pp trace))
        precondition
        postcondition
        t
        where
                precondition    = g `ps_contained_in` s &&
                                  read ret == 0 &&
                                  strace_syscall (snd trace) == "madvise"

                postcondition t = g `ps_contained_in` t

                p   = read addr   :: Integer
                len = read length :: Integer
                g   = region p len
                t   = ps_advise_vma g ad trace s



-- 18021 msync(0x2aaea77d4000, 1048576, MS_SYNC) = 0
ps_msync :: PState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PState
ps_msync s [addr, len, flags] ret trace =
        with_invariant "ps_msync"
        precondition
        postcondition
        t
        where
                precondition = g `ps_contained_in` s &&
                               read ret == 0 &&
                               strace_syscall (snd trace) == "msync"

                postcondition t = g `ps_contained_in` t

                g = region (read addr) (read len)
                t = ps_sync_vma g flags trace s


pt_exec :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_exec tid s args ret trace =
          with_invariant (report "pt_exec" (pp trace, pp_summary s))
          precondition
          postcondition
          t
        where
                precondition    = pt_member tid s && tid == strace_tid (snd trace) && ret == "0"
                postcondition s = pt_member tid s && ps_null_vm (s .! tid)

                t = pt_act_vm (const $ ps_empty tid trace) tid s


pt_clone_thread :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_clone_thread tid s args ret strace =
        with_invariant (report "pt_clone_thread" (tid,tid',s'))
        precondition
        postcondition
        s'
        where
                precondition    = pt_member tid  s && not (pt_member tid' s) &&
                                  tid' /= (-1) && tid' /= 0

                postcondition s = pt_member tid' s &&
                                  not (ps_null_vm (s .! tid')) &&
                                  (s .! tid) == (s .! tid')

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


pt_vfork :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_vfork tid s args ret strace =
        with_invariant "pt_vfork"
        precondition
        postcondition
        t
        where
                precondition    = pt_member tid  s &&
                                  not (pt_member child_pid s) &&
                                  child_pid /= (-1) &&
                                  strace_syscall (snd strace) == "vfork"

                postcondition s = pt_member child_pid s &&
                                  not (ps_null_vm (s .! child_pid))  &&
                                  (ps_vm $ s .! tid) == (ps_vm $ s .! child_pid)

                child_pid  = read ret :: Pid
                parent_pid = ps_pid (s .! tid )
                t         = pt_insert_process child_pid parent_pid strace s



pt_exit :: Tid -> PTState -> Integer -> UniqueStrace -> PTState
pt_exit tid s exit_code strace =
        with_invariant "pt_exit"
        precondition
        postcondition
        $ pt_delete_thread tid exit_code strace s
        where
                precondition    = strace_is_exit (snd strace)
                postcondition t = not (pt_member tid t)



read_int :: String -> Maybe Integer
read_int xs = case readSigned readDec xs of
        [] -> Nothing
        (a,_):_ -> Just a


-- Let's ignore for the moment
pt_wait :: Tid -> PTState -> SyscallArgs -> SyscallRet -> UniqueStrace -> PTState
pt_wait tid s args ret strace = s

pt_delete_thread :: Tid -> Integer -> UniqueStrace -> PTState -> PTState
pt_delete_thread tid code strace s =
        with_invariant (report "pt_delete_thread" (tid,s))
        precondition
        postcondition
        t
        where
                precondition    = warn (printf "pt_delete_thread:(pid,count)=(%d,%d)" pid count) $
                                  pt_member tid s && count > 0
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

every n [] = []
every n (x:xs) = x: every n (drop (n-1) xs)


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
test_memst =  readFile test_file             >>=
              return . parse                 >>=
              return . strace_with_id        >>=
              return . emulate_vm            >>=
              return . snapshot 100          >>=
              return . take 10               >>=
              putStrLn . render . pp_list . map (text . show)


test_matrix :: IO ()
test_matrix =  readFile test_file            >>=
               return . parse                >>=
               return . strace_with_id       >>=
               return . emulate_vm           >>=
               return . snapshot 100         >>=
               return . take 10              >>=
               return . map fst              >>=
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

tee_progress :: String -> Int -> [a] -> IO [a]
tee_progress id n xs =
        let xss = chunksOf n xs ++ [[]]
        in  fmap concat $ mapM progress $ zip [1..] xss

        where
                print_err :: String -> IO ()
                print_err x = hPutStrLn stderr x

                progress (i,[]) = do print_err $ printf "%s:finished" id
                                     return []
                progress (i,xs) = do print_err $ printf "%s:%d * %d\n" id (i::Int) n
                                     return xs



{-
************************************************************************
*                                                                      *
*              7. Lazy Stream IO
*                                                                      *
************************************************************************


-}

-- The fundamental problem is that Haskell's idea of 'RealWorld' dependency (the assumption
-- that it incrementally changes after each IO, or in other words the assumption that the RealWorld
-- is modeled by a free monoidal actions) doesn't necessarily reflect our common sense
-- knowledge about the  particular system we need to deal with.
--
-- Consider, for example, emulating "make" where file system objects can partially be assumed
-- 'referentially transparent', i.e. the contents of the file can mostly be determined by its
-- path and its modification time. In essense we have to model the true dependency of our IO based on
-- the specific assumptions we are making; there can be no one-fits-all solution. What we probably need is a
-- technology to model data dependency for our custom 'RealWorld', and a tool by which we can create a
-- custom 'OurIO' monad based on that dependency model.
--
-- One possible way to cleanly model that kind of dependency might be the Grothendieck topology (again!)
-- because clearly dependencies are 'stable under pullback' (that is, if X and Y depend on
-- some assumption Z then the (strict) pair (X,Y) will also depend on Z, and it will be universal in the
-- obvious sense.)
-- Thus we can consider a 'sheaf on dependency', and an IO action on
-- such a space would then be a path connecting two 'assumptions'
-- (not necessarily points; probably  locales.)

infixl 2 >>=~
m >>=~ f =  do x <- m
               unsafeInterleaveIO $ f x

-- |- Assumption:
-- each element in the resulting list depends on the shallow evaluation of the previous element, but no more.
-- (this is of course broken, just a quick hack)
for_stream :: NFData b => [a] -> (a -> IO b) -> IO [b]
for_stream [] f = return []
for_stream (x:xs) f = do
        y  <- f x
        ys <- unsafeInterleaveIO $ go y xs
        return (y:ys)

        where
                go y []     = y `seq` return []
                go y (x:xs) = y `seq` do
                        y' <- f x
                        ys <- unsafeInterleaveIO $ go y' xs
                        return (y':ys)

verbose_hclose :: Handle -> IO ()
verbose_hclose h = do info  "closing handle..."
                      hShow h >>= print
                      hClose h
                      hShow h >>= info
                      info "handle closed!"

        where
                info = hPutStrLn stderr

tee_to :: (Pretty a, NFData a) => FilePath -> (a -> Doc) -> [a] -> IO [a]
tee_to file pp xs = do
        h <- openFile file WriteMode

        let xs' = pair $ map Left xs ++ [Right $ verbose_hclose h]

        for_stream xs' (tee' h)

        where
                tee' h (Left x, Left x') = do  render_line_to h $ pp x
                                               return x
                tee' h (Left x, Right job) = do render_line_to h $ pp x
                                                job
                                                return x
                pair xs = zip xs (tail xs)



tee :: (Pretty a, NFData a) => Handle -> (a -> Doc) -> [a] -> IO [a]
tee h pp xs = for_stream xs $ \x -> do
        render_line_to h $ pp x
        return x


-- Show line number and pass input through
-- man nl(1)
nl :: (Pretty a, NFData a) => Handle -> [a] -> IO [a]
nl h xs = return (zip [1..]  xs) >>=
          tee h (int . fst) >>=
          return . map snd

nl_format :: (Pretty a, NFData a) => Handle -> ((Int,a) -> Doc) -> [a] -> IO [a]
nl_format h pp xs = return (zip [1..]  xs) >>=
                  tee h pp                 >>=
                  return . map snd

nl_label h label = nl_format h (\(n,_) -> text $ printf "%s:%d" label n)

wc :: FilePath -> IO Int
wc file = readFile file >>=
          return . lines >>=
          return . force . length



render_line_to :: Handle -> Doc -> IO ()
render_line_to h doc = hPutStrLn h $ myrender doc


read_strace :: FilePath -> IO [UniqueStrace]
read_strace in_file =  readFile in_file        >>=
                       return . parse          >>=
                       return . map force      >>=
                       return . strace_with_id


write_data_frame' :: FilePath -> [PTState] -> IO ()
write_data_frame' file ss =  writeFile file $ render $ pp_data_frame  $ ss

write_data_frame :: FilePath -> [PTState] -> IO ()
write_data_frame file ss = withFile file WriteMode $ write_data_frame_to_handle ss

write_data_frame_to_handle :: [PTState] -> Handle -> IO ()
write_data_frame_to_handle ss h = put_header h >> go ss
        where
                go [] = return ()
                go (s:ss) = do put_data h s
                               go ss

                put_header h = render_line_to h $ pp_data_frame_header
                put_data h s = render_line_to h $ pp_pt_data_frame s


tee_data_frame :: FilePath -> [PTState] -> IO [PTState]
tee_data_frame file xs = tee_to file pp (Nothing : map Just xs) >>=
                         return . catMaybes
        where
                pp Nothing  = pp_data_frame_header
                pp (Just x) = pp_pt_data_frame x


write_stack_trace :: FilePath -> [(PTState,UniqueStrace)] -> IO ()
write_stack_trace file ts  = let body   = vcat (map pp_trace ts)
                                 doc    = pp_trace_header $$ body
                             in
                                     writeFile file $ render doc

tee_stack_trace :: FilePath -> [(PTState, Maybe UniqueStrace)] -> IO [(PTState, Maybe UniqueStrace)]
tee_stack_trace file xs = tee_to file pp (Nothing : map Just xs) >>=
                          return . catMaybes
        where
                pp :: Maybe (PTState, Maybe UniqueStrace) -> Doc
                pp Nothing  = pp_trace_header
                pp (Just (pt,Just t)) = pp_trace (pt,t)
                pp (Just (pt, Nothing)) = pp_empty


pp_status_line :: (PTState, Maybe UniqueStrace) -> Doc
pp_status_line (pt, Nothing)   = text "status:<empty trace>" $$ pp pt
pp_status_line (pt,Just (n,t)) =
        text $ render_left $ text "status" <:> id <:> num_process <:> trace_summary
        where
                x <:> y = x <> text ":" <> y
                id = pp n
                num_process   = int $ pt_num_processes pt
                trace_summary = pp_level 0 t

dump :: FilePath -> FilePath -> FilePath -> IO ()
dump strace_in frame_out trace_out = do
        ln <- wc strace_in
        let nl name = nl_format stderr (label name ln)

        traces <- readFile strace_in       >>=
                  return . parse           >>=
                  nl "line"                >>=
                  return . strace_with_id  >>=
                  nl "strace"              >>=
                  return

        let tn = length traces
            k  = max 1 (tn `div` sample_size)
            nl  name = nl_format stderr (label name tn)
            nl' name = nl_format stderr (label name sample_size)

        () <- return traces              >>=
              return . emulate_vm        >>=
              nl "emulate_vm"            >>=
              tee stderr pp_status_line  >>=
              tee_stack_trace trace_out  >>=
              nl "tee_stack_trace"       >>=
              return . map fst           >>=
              return . every k           >>=
              nl' "summarize"            >>=
              tee_data_frame frame_out   >>=
              nl' "tee_data_frame"       >>=
              finish
              --write_data_frame frame_out

        return ()

        where
                sample_size = 1000
                label name m (n,x) = text $ printf "%s:%d/%d" name n m
                finish xs = putStrLn $ printf "%d frames written" $ length xs
                --summarize = assert' "valid" (all pt_valid) . snapshot 1000


dump' :: FilePath -> FilePath -> FilePath -> IO ()
dump' strace_in frame_out trace_out =
        readFile strace_in >>=
        return . parse >>=
        return . map force >>=
        return . strace_with_id >>=
        return . emulate_vm >>=
        return . summarize >>=
        return . zip [1..] >>=
        return . map force >>=
        tee stderr (int . fst) >>=
        const (return ())
        where
                summarize xs = snapshot 500 $ hyper_take 5000 xs



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
