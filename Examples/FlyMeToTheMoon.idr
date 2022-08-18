||| An example of oloing over the 'Fly Me To The Moon' chord progression. Not
||| fully finished.
module Examples.FlyMeToTheMoon

import Melocule
import System

fmttm : MonadSample m => m Tune
fmttm = do
  let c = the (Scale MajorS) Ionian
      a = the (Scale MinorS) Melodic
  cs <- map concat $ replicateM 5 $ genBar straight16s 96 c cM7
  as <- map (transpose (minus A 12) . concat) $ replicateM 3 $ genBar straight16s 96 a am7
  pure $ cs ++ as

writeFmttm : String -> IO ()
writeFmttm fn = writeTuneDefault !(sampleIO fmttm) flyMeToTheMoon fn


||| Reads the first argument as a filename, and writes a generated tune to it.
main : IO ()
main = case !getArgs of
  []     => printLn "expected filename"
  (fn::_) => writeFmttm fn
