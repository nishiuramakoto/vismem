module Main
where

import Data.Maybe
import Data.List
import Data.List.Split
import Data.Char
import Data.Hashable
import Data.Bits
import Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IntervalMap
import qualified Data.IntervalMap.Interval as Interval

import Control.Exception

import Text.Printf
import Text.PrettyPrint
import Text.Regex.PCRE

import System.IO.Unsafe


{-
************************************************************************
*                                                                      *
*              The main types
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
            { sl_tid     :: Integer
            , sl_syscall :: String
            , sl_ret     :: SyscallRet
            }
          | SyscallResumedError
            { sl_tid     :: Integer
            , sl_syscall :: String
            , sl_ret     :: SyscallRet
            , sl_err     :: String
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
*              Strace output parser
*                                                                      *
************************************************************************

   Run strace as:
   # strace -e trace=memory -k command
   You may need to compile strace, as '-k' is documented as an experimental feature

   @tbd: parse '-t', '-tt', etc.
-}

-- 18232 mmap(NULL, 8192, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = 0x7f3927f2a000
parse_syscall_entry :: String -> Maybe (String, String, String, String)
parse_syscall_entry x =
        let matches = x  =~ "^(\\d+) +(\\w+) *\\(([^)]*)\\) *= *([\\S]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, args, ret]] -> Just (tid, syscall, args, ret)
                otherwise                   -> Nothing

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
                otherwise                   -> Nothing

-- 18253 <... mmap resumed> )              = 0x7f390ac62000
parse_syscall_resumed :: String -> Maybe (String, String, String)
parse_syscall_resumed x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *\\) *= *([\\S]+) *$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, ret]] -> Just (tid, syscall, ret)
                otherwise                -> Nothing

-- 18253 <... mmap resumed> )              = -1 ENOMEM.*
parse_syscall_resumed_error :: String -> Maybe (String, String, String, String)
parse_syscall_resumed_error x =
        let matches = x  =~ "^(\\d+) +<\\.\\.\\. *(\\w+) +resumed *> *\\) *= *([\\S]+) +(\\w.*)$" :: [[String]]
        in
                case matches of
                [[_, tid, syscall, ret, err]] -> Just (tid, syscall, ret, err)
                otherwise                     -> Nothing


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
                syscall_resumed     (tid, syscall, ret)
                        = SyscallResumed (i tid) syscall ret
                syscall_resumed_error (tid, syscall, ret, err)
                        = SyscallResumedError (i tid) syscall ret err
                stack_trace (trace)
                        = StackTrace trace
                exit (tid, status)
                        = Exit (i tid) (i status)
                signal (tid, signal, args)
                        = Signal (i tid) signal (split args)
                i = read
                split = map chomp . splitOn ","

chomp = strip_left . strip_right
strip_right = reverse . strip_left . reverse
strip_left  = dropWhile isSpace

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
                (SyscallResumed tid' syscall' ret', traces, rest') ->
                        if tid == tid' && syscall == syscall'
                        then
                                (Strace tid syscall args ret' traces) : strace rest'
                        else
                                error $ "strace unfinished:" ++ show tid ++ show syscall
                -- skip errors
                (SyscallResumedError tid' syscall' ret' err, traces, rest') ->
                        if tid == tid' && syscall == syscall'
                        then
                                strace rest'
                        else
                                error $ "strace unfinished:" ++ show tid ++ show syscall

                _ ->            error $ "strace unfinished:" ++ show tid ++ show syscall

strace (SyscallResumed tid syscall ret: rest) =
        error $ "resumed without unfinished:" ++ show tid ++ syscall
strace (SyscallResumedError tid syscall ret err: rest) =
        error $ "resumed without unfinished:" ++ show tid ++ syscall
strace (StackTrace call_stack: rest)               =
        error $ "trace without syscall line:"
        ++ show call_stack ++ (render $ pp_list $ map pp_line $ take 30 rest)

-- skip
strace (Exit   tid status: rest)      = strace rest
strace (Signal tid signal args: rest) = strace rest

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
                is_resumed tid syscall (SyscallResumed tid' syscall' ret') =
                        tid == tid' && syscall == syscall'
                is_resumed tid syscall (SyscallResumedError tid' syscall' ret' err') =
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
*              Pretty printers
*                                                                      *
************************************************************************
-}


pp_line :: StraceLine -> Doc
pp_line l = text (show l)


pp_list :: [Doc] -> Doc
pp_list = vcat


pp_strace :: Strace -> Doc
pp_strace (Strace tid syscall args ret trace) =
        text syscall <> parens (f args) <+> text "=" <+> text ret $$ nest 5 (pp_list (map pp_line trace))
        where
                f = sep . punctuate comma . map text


pp_matrix :: [State] -> Doc
pp_matrix ss = vcat $ map pp_row $ zip [1..] ss

pp_row :: (Int, State) -> Doc
pp_row (n, State tree) = vcat $ map (pp_vma n) $  IntervalMap.toAscList tree

pp_vma :: Int -> (Region, VMAInfo) -> Doc
pp_vma n (i, v) = int n <+> low i <+> high i <+> valuation v <+> trace_id v
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


pp_trace ::  UniqueStrace -> Doc
pp_trace (n, Strace tid syscall args ret trace) = int n <+> doubleQuotes trace_doc
        where
                args'       = hsep $ punctuate comma (map text args)
                funcall     = integer tid <+> text syscall <> parens args' <+> equals <+> text ret
                trace_lines = map sl_call_stack trace
                trace_doc   = vcat $ funcall : map text trace_lines


{-
************************************************************************
*                                                                      *
*              Linux VMA emulator for x86
*                                                                      *
************************************************************************
-}

page_shift = 12



data VMAInfo = VMAInfo
               { vma_prot   :: String
               , vma_flags  :: String
               , vma_fd     :: String
               , vma_offset :: String
               , vma_trace  :: UniqueStrace
               }
            deriving (Eq,Show)

instance Hashable VMAInfo where
        hashWithSalt n (VMAInfo a b c d _) = hashWithSalt n (a,b,c,d)

type Region = IntervalMap.Interval Integer

data State = State
             { vma_tree :: IntervalMap Integer VMAInfo
             }
             deriving (Eq,Show)

empty_state :: State
empty_state = State (IntervalMap.empty)

-- |Main VMA emulator function
emulate_vma :: [(Id,Strace)] -> [State]
emulate_vma syscalls = scanl action empty_state syscalls
        where
                action s (n,syscall) = mem_action s (n,syscall) :: State


disjoint :: State -> Bool
disjoint (State tree) = disjoint_interval_tree tree

paged :: State -> Bool
paged (State tree) = all paged' $ IntervalMap.keys tree
        where
                mask = 1 `shiftL` page_shift - 1

                paged' iv = let (x,y) = nonstd iv
                                (a,b) = (nonstd_proj x, nonstd_proj y)
                            in
                                    a .&. mask == 0 && b .&. mask == 0

disjoint_interval_tree tree = all disjoint' $ rel  $ IntervalMap.keys tree
        where
                rel xs = zip xs (tail xs)
                disjoint'  (i, j) = let (x,y) = nonstd i
                                        (z,w) = nonstd j
                                    in  y < z

region :: Integer -> Integer -> Region
region p len = IntervalMap.IntervalCO p (p+len)

align_page :: Region -> Region
align_page i = let (x,y)      = nonstd i
                   align_floor x = (x `shiftR` page_shift) `shiftL` page_shift
                   align_ceil  x = (x `shiftR` page_shift + 1) `shiftL` page_shift
               in
                       from_nonstd (align_floor x, align_ceil y)


insert_vma :: (Integer, Integer) -> (String, String, String, String) -> UniqueStrace -> State -> State
insert_vma (p,len) (prot,flags,fd,offset) trace s =
        with_invariant "insert_vma" precondition postcondition (State tree'')

        where
                precondition    = disjoint s && paged s
                postcondition x = disjoint x && paged x

                State tree'  = delete_vma (p,len) trace s
                iv           = align_page $ region p len
                tree''       =  IntervalMap.insert
                                iv
                                (VMAInfo prot flags fd offset trace)
                                tree' :: IntervalMap Integer VMAInfo

delete_vma :: (Integer, Integer) -> UniqueStrace -> State -> State
delete_vma (p,len) trace (State tree) =
        with_invariant "delete_vma" precondition postcondition (State tree')

        where
                precondition    = disjoint s && paged s where s = State tree
                postcondition x = disjoint x && paged x

                iv    = align_page $ region p len

                tree' = let (below, cross, above) = IntervalMap.splitIntersecting tree iv
                            cross_list            = IntervalMap.toAscList cross
                            cross_list'           = concat $ map del cross_list
                            cross'                = IntervalMap.fromList cross_list'
                        in
                                below <++> cross' <++> above

                del =  uncurry zip . ((`interval_diff` iv) >< repeat)
                       :: (Region, VMAInfo) -> [(Region,VMAInfo)]

                a <++> b = IntervalMap.union a b
                (f >< g) (x,y) = (f x, g y)


update_vma :: (Integer, Integer) -> String -> UniqueStrace -> State -> State
update_vma (p,len) prot trace (State tree) = State tree'
        where
                tree' = IntervalMap.update
                        update
                        (region p len)
                        tree
                update vma = Just vma { vma_prot = prot , vma_trace = trace }


-- |VMA state transition function
-- Use sequence number to identify stack traces
mem_action :: State -> UniqueStrace -> State
mem_action s t@(n, Strace tid "mmap"     args ret trace) = mmap     s args ret t
mem_action s t@(n, Strace tid "mmap2"    args ret trace) = error "mmap2 is unsupported"
mem_action s t@(n, Strace tid "munmap"   args ret trace) = munmap   s args ret t
mem_action s t@(n, Strace tid "mprotect" args ret trace) = mprotect s args ret t
mem_action s _ = s  -- Ignore other syscalls at the moment


mmap :: State -> SyscallArgs -> SyscallRet -> UniqueStrace -> State
mmap s [addr, length, prot, flags, fd, offset] ret trace =
        let p    = read ret    :: Integer
            len  = read length :: Integer
            anon = "MAP_ANON" `isInfixOf` flags  :: Bool
        in
                insert_vma (p,len) (prot, flags, fd, offset) trace s

munmap :: State -> SyscallArgs -> SyscallRet -> UniqueStrace -> State
munmap s [addr, length] ret trace =
        let p   = read addr   :: Integer
            len = read length :: Integer
        in
                delete_vma (p,len) trace s

mprotect :: State -> SyscallArgs -> SyscallRet -> UniqueStrace -> State
mprotect s [addr, length, prot] ret trace =
        let p   = read addr   :: Integer
            len = read length :: Integer
        in
                update_vma (p,len) prot trace s


interval_diff :: Region -> Region -> [Region]
interval_diff i j = map from_nonstd $
                    interval_merge' $
                    filter (not . interval_null') $
                    interval_diff' (nonstd i) (nonstd j)
        where
                interval_diff' i@(ix,iy)  j@(jx,jy)
                        | jx < ix && jy <   ix    = [i]
                        | jx < ix && jy <=  iy    = [(jy + epsilon, iy)]
                        | jx < ix && iy <   jy    = []
                        | jx == ix && jy <= iy    = [(jy + epsilon, iy)]
                        | jx == ix && iy <  jy    = []
                        | ix < jx  && jy <  iy    = [(ix,jx -epsilon),(jy + epsilon,iy)]
                        | ix < jx  && iy <= jy    = [(ix,jx -epsilon)]
                        | iy == jx                = [(ix,jx -epsilon)]
                        | iy <  jx                = [i]

-----------------------------------------------------------
--    A non standard integer model represented as Z*Q    --
-----------------------------------------------------------

data NonStdInteger = NonStd { nonstd_proj    :: Integer
                            , nonstd_epsilon :: Rational
                            }
                   deriving(Eq,Ord,Show)

type NonStdInterval = (NonStdInteger, NonStdInteger)

-- Special constant representing the unit positive infinitesimal
epsilon :: NonStdInteger
epsilon = NonStd 0 1

-- lift to the sheaf
lift_nonstd :: (Integer -> Integer) -> NonStdInteger -> NonStdInteger
lift_nonstd f (NonStd x e)  = NonStd (f x) e

instance Num NonStdInteger where
        negate (NonStd x e) = NonStd (negate x) (negate e)
        (NonStd x e) + (NonStd x' e') = NonStd (x+x') (e+e')
        (NonStd x e) * (NonStd x' e') = NonStd (x*x') (e*e')
        fromInteger x = NonStd (fromInteger x) 0
        abs    (NonStd x e) = NonStd (abs x) e
        signum (NonStd x e) = NonStd (signum x) e

instance Bits NonStdInteger where
        (NonStd x e) `shiftL` n = NonStd (x `shiftL` n) e
        (NonStd x e) `shiftR` n = NonStd (x `shiftR` n) e
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

interval_null' :: NonStdInterval -> Bool
interval_null' (a,b) = b < a

interval_merge' :: [(NonStdInteger,NonStdInteger)] -> [(NonStdInteger,NonStdInteger)]
interval_merge' []  = []
interval_merge' [x] = [x]
interval_merge' (x:y:zs)
        | mergeable x y = interval_merge' (merge x y: zs)
        | otherwise     = x : interval_merge' (y:zs)
        where
                mergeable (x,y) (z,w) = y < z && nonstd_proj y == nonstd_proj z
                merge     (x,y) (z,w) = (x,w)



nonstd :: Region -> (NonStdInteger, NonStdInteger)
nonstd iv = case iv of
        (IntervalMap.IntervalCO x y)     -> (i x, i y - epsilon)
        (IntervalMap.ClosedInterval x y) -> (i x,i y)
        (IntervalMap.OpenInterval x y)   -> (i x+epsilon, i y-epsilon)
        (IntervalMap.IntervalOC x y)     -> (i x+epsilon, i y)
        where
                i = fromInteger

from_nonstd (NonStd x e, NonStd y f)
        | e == 0 && f == 0 = IntervalMap.ClosedInterval x y
        | e == 0 && f <  0 = IntervalMap.IntervalCO x y
        | e >  0 && f == 0 = IntervalMap.IntervalOC x y
        | e >  0 && f <  0 = IntervalMap.OpenInterval x y
        | otherwise = error $ "invalid interval:" ++ show (NonStd x e,NonStd y f)



--------------------------------------------
--    IO and testing                      --
--------------------------------------------

snapshot n xs  = every (length xs `div` n) xs
every n xs     = map head $ chunksOf n xs


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
                 | otherwise = error $ "assertion failed:" ++ desc ++ ":" ++ show x

test' desc p x | p x = True
               | otherwise = error $ "test failed:" ++ desc ++ ":" ++ show x


with_invariant :: Show a => String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret =
        assert' (desc ++ ":precondition:") (const pre) $
        assert' (desc ++ ":postcondition") post        $
        ret


test_memst :: IO ()
test_memst =  readFile test_file                         >>=
              return . parse                             >>=
              return . strace_with_id                    >>=
              return . emulate_vma                       >>=
              return . snapshot 100                      >>=
              return . map (assert' "disjoint" disjoint) >>=
              return . take 10                           >>=
              putStrLn . render . pp_list . map (text . show)


test_matrix :: IO ()
test_matrix =  readFile test_file                         >>=
               return . parse                             >>=
               return . strace_with_id                    >>=
               return . emulate_vma                       >>=
               return . snapshot 100                      >>=
               return . map (assert' "disjoint" disjoint) >>=
               return . take 10                           >>=
               putStrLn . render . pp_matrix


read_strace :: FilePath -> IO ([State], [UniqueStrace])
read_strace in_file =  readFile in_file        >>=
                       return . parse          >>=
                       return . strace_with_id >>=
                       ((return . emulate_vma) >< (return . id))

write_matrix :: FilePath -> [State] -> IO ()
write_matrix file ss = let header = text "t from to v trace_id"
                           body   = pp_matrix ss
                           doc    = header $$ body
                       in
                               writeFile file $ render doc


write_stack_trace :: FilePath -> [UniqueStrace] -> IO ()
write_stack_trace file ts  = let header = text "trace_id trace"
                                 body   = vcat (map pp_trace ts)
                                 doc    = header $$ body
                             in
                                     writeFile file $ render doc


-- trace without syscall line "/lib/x86_64-linux-gnu/libc-2.19.so(madvise+0x7) [0xf4967]
test :: IO ()
test =  readFile test_file      >>=
        return . parse  >>=
        return . strace >>=
        return . take 10 >>=
        putStrLn . render . pp_list . map pp_strace

test_file   = "cassandra.strace"
matrix_file = "out.data"
trace_file  = "trace.data"

dump = read_strace test_file >>=
       ((write_matrix matrix_file . summarize) ***  write_stack_trace trace_file )
        where
                summarize = assert' "disjoint" (all disjoint) . snapshot 1000

main :: IO ()
main  =  getContents >>=
         return . parse >>=
         print
