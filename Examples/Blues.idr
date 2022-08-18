||| A couple of examples of soloing over the twelve-bar-blues progression.
module Examples.Blues
-- TODO: This would be a nice place to show off random chord exts, if added

import Melocule
import System

||| Solos for n bars over an implied twelve bar blues progression.
nBarBlues : MonadSample m => Nat -> m Tune
nBarBlues n = do
  scale <- bluesOrPenta
  ns <- replicateM n (genBar straight16s 96 scale cd7) -- TODO: take chordprog and change this
  pure $ concat ns
  where bluesOrPenta : m (Scale MajorS)
        bluesOrPenta = uniformD [Blues, Pentatonic]

write12bb : String -> IO ()
write12bb fn = writeTuneDefault !(sampleIO $ nBarBlues 12) twelveBarBlues fn

write12bbf : String -> IO ()
write12bbf fn = writeTuneDefault !(sampleIO $ nBarBlues 24) twelveBarBluesFancy fn


||| Reads the first argument as a filename, and writes a generated tune to it.
main : IO ()
main = case !getArgs of
  []     => printLn "expected filename"
  (fn::_) => write12bbf fn
