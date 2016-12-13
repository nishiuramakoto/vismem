{-# LANGUAGE CPP #-}
module Invariant(
        trace,
        assert',
        warn,
        warn_if,
        with_invariant
        )
       where

import System.IO.Unsafe

trace :: Show a => a -> a
trace x = unsafePerformIO $ do
        print x
        return x

assert' :: String -> (a -> Bool) -> a -> a
assert' desc p x | p x = x
                 | otherwise = error $ "assertion failed:" ++ desc

test' :: String -> (a -> Bool) -> a -> Bool
test' desc p x | p x = True
               | otherwise = error $ "test failed:" ++ desc

warn :: String -> a -> a
warn desc x = unsafePerformIO $ do
        putStrLn $ "warning:" ++ desc
        return x

warn_if :: (a -> Bool) -> String -> a -> a
warn_if p desc x
        | p x       = warn desc x
        | otherwise = x


#ifndef NDEBUG

with_invariant :: String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret =
        assert' (":postcondition:" ++ desc) post        $
        assert' (":precondition:"  ++ desc) (const pre) $
        ret

#else

with_invariant :: String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret = ret

#endif
