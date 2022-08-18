||| A simple example for showcasing soloing with random scales over a hard-coded
||| chord progression.
module Examples.TwoFive

import Melocule
import System

||| Prior distribution for a two-five-one chord progression in C Major, with
||| randomly chosen scales above each chord.
partial
twoFivePrior : MonadSample m => Nat -> m Tune
twoFivePrior n = do
  sTwo  <- genScale MinorS [0.125, 0.125, 0.25, 0.5]
  sFive <- genScale MajorS [1/6, 1/3, 1/4, 1/4]
  sOne  <- genScale MajorS [1/12, 1/12, 3/6, 2/6]

  tuneTwo  <- genBar straight16s n sTwo dm7
  tuneFive <- genBar straight16s n sFive gd7
  tuneOne  <- genBar straight16s n sOne cM7

  pure $ (transpose second tuneTwo) ++ (transpose fifth tuneFive) ++ tuneOne

write251 : String -> IO ()
write251 fn = do
  t <- sampleIO $ twoFivePrior 96
  writeTuneDefault t twoFive fn

||| Reads the first argument as a filename, and writes a generated tune to it.
main : IO ()
main = case !getArgs of
  []     => printLn "expected filename"
  (fn::_) => write251 fn
