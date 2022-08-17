||| A couple of examples of soloing over the twelve-bar-blues progression.
module Examples.Blues
-- TODO: This would be a nice place to show off random chord exts, if added

import Melocule

||| Solos for n bars over an implied twelve bar blues progression.
nBarBlues : MonadSample m => Nat -> m Tune
nBarBlues n = do
  scale <- bluesOrPenta
  ns <- replicateM n (genBar straight16s 96 scale cd7) -- TODO: take chordprog and change this
  pure $ concat ns
  where bluesOrPenta : m (Scale MajorS)
        bluesOrPenta = uniformD [Blues, Pentatonic]

test12bb : String -> IO ()
test12bb fn = writeTuneDefault !(sampleIO $ nBarBlues 12) twelveBarBlues fn

test12bbf : String -> IO ()
test12bbf fn = writeTuneDefault !(sampleIO $ nBarBlues 24) twelveBarBluesFancy fn
