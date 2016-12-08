module Invariant(
        trace,
        assert',
        with_invariant
        )
       where

import System.IO.Unsafe

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
with_invariant :: String -> Bool -> (a -> Bool) -> a -> a
with_invariant desc pre post ret = ret'
        where
                ret' =  assert' (":precondition:"  ++ desc) (const pre) $
                        assert' (":postcondition:" ++ desc) post        $
                        ret
