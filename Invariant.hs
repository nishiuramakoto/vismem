{-# LANGUAGE CPP #-}
module Invariant(
        trace,
        assert',
        warn,
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

-- Never rely on the evaluation order..
warn :: String -> a -> a
warn desc x = unsafePerformIO $ do
        putStrLn $ "warning:" ++ desc
        return x


#ifndef NDEBUG

with_invariant :: String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret = ret'
        where
                ret' =  assert' (":precondition:"  ++ desc) (const pre) $
                        assert' (":postcondition:" ++ desc) post        $
                        ret

#else

with_invariant :: String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret = ret

#endif
