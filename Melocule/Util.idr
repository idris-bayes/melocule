||| These should ideally be in the stdlib.
module Melocule.Util

import Data.Buffer
import Data.List

||| `replicateM` performs the monadic action `a` `n` times, and returns a list of
||| the results of each action.
export
replicateM : Applicative m => (n : Nat) -> m a -> m (List a)
replicateM n xs = sequence $ replicate n xs

||| The scanl function is similar to foldl, but returns all the intermediate
||| accumulator states in the form of a list.
export
scanl : forall elem. (res -> elem -> res) -> res -> List elem -> List res
scanl f x [] = [x]
scanl f x (y :: xs) = x :: scanl f (f x y) xs

||| Sets the data of a buffer from a list of ints. They should all be Byte8s,
||| but since `setData . getData` should roughly be an identity, we're stuck with this.
export
setData : Buffer -> List Int -> IO ()
setData b is = sequence_ $ zipWith (setByte b) [0 .. cast (length is) - 1] is
