module Melocule

import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Data.Buffer
import Data.List1
import Data.List
import Data.Vect
import Generics.Derive
import Sound.Midi.Types
import Sound.Midi.Serialise
import Syntax.WithProof
import System.File.Buffer

import Music.Theory


replicateM : Applicative m => (n : Nat) -> m a -> m (List a)
replicateM n xs = sequence $ replicate n xs

||| Direction for a meldoy fragment to proceed in.
data Dir = Up
         | Down
dirs : Vect ? Dir
dirs = [Up, Down]

||| Melody Fragments used for constructing tunes.
data MelodyFrag = ||| Distribute notes uniformly through a scale.
                  Uniform
                | ||| Arpeggiate the underlying chord.
                  Arpeggio
                | ||| Walk through the scale.
                  Walk
mfrags : List MelodyFrag
mfrags = [Uniform, Arpeggio, Walk]


catIndex : MonadSample m => (weights : List Double) -> (categories : List s) ->
  (0 ford : length weights === length categories) =>
  m s
catIndex ps ss = do
  let ps' := Vect.fromList ps
      ss' := Vect.fromList ss
  pure $
    index !(categorical $ rewrite sym ford in ps') $ ss'

uniformScale : MonadSample m => {q : ScaleQual} -> Nat -> Scale q -> m (List Note)
uniformScale n s = assert_total $ do
  let ns = scaleToNotes q s
      (S n ** prf) := @@(length ns)
      | _ => pure []
  replicateM n $ uniformD
               $ replace {p = \u => Vect u Nat} prf
               $ fromList ns

endless : forall elem'. List elem' -> Stream elem'
endless xs = endlessAux xs
  where
    endlessAux : List elem' -> Stream elem'
    endlessAux [] = endlessAux xs
    endlessAux (y :: ys) = y :: endlessAux ys

runDir : Dir -> Nat -> List a -> List a
runDir Up   n = take n . endless
runDir Down n = reverse . take n . endless

scaleDir : {q : ScaleQual} -> Scale q -> Dir -> (n : Nat) -> List Nat
scaleDir s d n = runDir d n $ scaleToNotes q s

arpeggiate : MonadSample m => Nat -> Chord -> m (List Note)
arpeggiate n (MkChord _ _ ns) = do
  d <- uniformD dirs
  let ns' := runDir d n $ toList ns
  pure ns'

walk : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Nat)
walk n s = do
  dir <- uniformD dirs
  pure $ scaleDir s dir n

genMelodyFrag : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> Chord -> m (List Note)
genMelodyFrag n s c = do
  case !(uniformD $ fromList' [] mfrags) of
    Uniform  => uniformScale n s
    Arpeggio => arpeggiate n c
    Walk     => walk n s

-- TODO: put in stdlib's contrib
scanl : forall elem. (res -> elem -> res) -> res -> List elem -> List res
scanl f x [] = [x]
scanl f x (y :: xs) = x :: scanl f (f x y) xs

||| Generates a random number of nats that sum to n. The numbers are generated geometrically,
||| meaning lower p-values tend to give shorter lists of larger numbers.
fragment : MonadSample m => (n : Nat) -> Double -> m (List Nat)
fragment n p = do
  ns <- replicateM n $ geometric p
  pure $ case last' $ takeWhile (\x => fst x <= n)
       $ scanl (\(acc, l),e=>(acc+e, snoc l e)) (0, Prelude.Nil) ns of
    Nothing       => [n]
    Just (l, ns') => if n == l
                        then ns'
                        else snoc ns' $ n `minus` l

genMelody : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> Chord -> m (List Note)
genMelody n s c = do
  ls <- fragment n 0.2
  nss <- sequence $ map (\l => genMelodyFrag l s c) ls
  pure $ concat nss

||| Generates random durations that add up to n. `p` determines likelihood of
||| shorter durations.
genRhythm : MonadSample m => (n : Nat) -> Double -> m (List Duration)
genRhythm = fragment

partial
genBar : MonadSample m => {q : ScaleQual} -> Nat -> Scale q -> Chord -> m Tune
genBar n s c = do
  durs1 <- genRhythm (n`div`2) 0.62
  durs2 <- genRhythm (n`div`2) 0.62
  let durs = durs1 ++ durs2
      l    = length durs
  notes <- genMelody l s c
  pure $ zip notes durs

genScale : MonadSample m => (q : ScaleQual) -> (weights : List Double) ->
  (0 ford : length weights = nScales q) =>
  m (Scale q)
genScale MajorS ps = catIndex ps majScales
genScale MinorS ps = catIndex ps minScales

transpose : Note -> Tune -> Tune
transpose n = map (mapFst (+ n))

requantise : Nat -> Sequence a -> Sequence a
requantise n = map (mapSnd (* n))

partial
twoFivePrior : MonadSample m => Nat -> m Tune
twoFivePrior n = do
  sTwo  <- genScale MinorS [0.125, 0.125, 0.25, 0.5]
  sFive <- genScale MajorS [1/6, 1/3, 1/4, 1/4]
  sOne  <- genScale MajorS [1/12, 1/12, 3/6, 2/6]

  tuneTwo  <- genBar n sTwo dm7
  tuneFive <- genBar n sFive gd7
  tuneOne  <- genBar n sOne cM7

  pure $ (transpose second tuneTwo) ++ (transpose fifth tuneFive) ++ tuneOne

cycleFive : MonadSample m => m Tune
cycleFive = do
  pure []

nBarBlues : MonadSample m => Nat -> m Tune
nBarBlues n = do
  scale <- bluesOrPenta
  ns <- replicateM n (genBar 16 scale cd7) -- TODO: take chordprog and change this
  pure $ concat ns
  where bluesOrPenta : m (Scale MajorS)
        bluesOrPenta = uniformD [Blues, Pentatonic]

ppTune : Tune -> IO ()
ppTune = printLn . map (mapFst ppNote)

altMapAcc : Nat -> (a -> a) -> List a -> List a
altMapAcc acc f [] = []
altMapAcc acc f (x :: xs) = (if acc `mod` 2 == 0 then f x else x)
                         :: altMapAcc (S acc) f xs

||| Maps over alternating elements in a list. altMap maps from the first element,
||| altMap' from the second.
altMap, altMap' : (a -> a) -> List a -> List a
altMap  = altMapAcc 0
altMap' = altMapAcc 1

data Swing = Straight | Swung | Shuffled

playIt : Swing -> Sequence a -> Sequence a
playIt Straight = requantise 6
playIt Swung    = requantise 4 . altMap (mapSnd (* 2))
playIt Shuffled = requantise 3 . altMap (mapSnd (* 3))

-- ||| swingIt and shuffleIt both multiply the quantisation in order to
-- ||| alter where the notes land.
-- swingIt, shuffleIt : Tune -> ChordProg -> Tune
-- swingIt   = altMap (mapSnd (* 2))
-- shuffleIt = altMap (mapSnd (* 3))

dur2dT : Int -> Duration -> Nat -> Int
dur2dT tpqn d q = cast d * (tpqn `div` (cast q `div` 4))

immediately : TrkEvent -> TrkEvent
immediately (TE _ e) = TE 0 e

midiPlayNote : Int -> Nat -> Channel -> Note -> Duration -> List TrkEvent
midiPlayNote tpqn q c n d = [ TE 0                 $ MidiEvt $ MkChMsg c $ NoteOn  (cast n) 64
                            , TE (dur2dT tpqn d q) $ MidiEvt $ MkChMsg c $ NoteOff (cast n) 64 ]

noteToMidiCode : Int -> Nat -> (Note, Duration) -> List TrkEvent
noteToMidiCode tpqn q (n, d) = midiPlayNote tpqn q 0 (n + 60) (d`div`6)

notesToMidiCodes : Int -> Nat -> Tune -> List TrkEvent
notesToMidiCodes tpqn q = concat . map (noteToMidiCode tpqn q)

||| Converts a series of notes to be played into a single chord
||| This prevents cascading delta-times.
parallel : List1 (List TrkEvent) -> List (List TrkEvent)
parallel (t:::ts) = transpose $ t :: map (map immediately) ts

-- hacky
chordToMidiCodes : Int -> Nat -> Chord -> List TrkEvent
chordToMidiCodes tpqn q (MkChord _ _ ns) = concat
                                         $ parallel
                                         $ map (\n => toList
                                                    $ midiPlayNote tpqn q 0 (n + 48) q)
                                               ns

midiTrk : List TrkEvent -> Chunk
midiTrk ns = Track $ ns ++ [TE 1 $ MetaEvt $ EndOfTrack]

genMidiFile : Int -> Nat -> List Chord -> Tune -> MidiFile
genMidiFile tpqn q cs t = [ Header 1 2 tpqn
                          , midiTrk $ notesToMidiCodes tpqn q t
                          , midiTrk $ concat $ map (chordToMidiCodes tpqn q) cs ]

setData : Buffer -> List Int -> IO ()
setData b is = sequence_ $ zipWith (setByte b) [0 .. cast (length is) - 1] is

partial
test : Int -> Nat -> Tune -> ChordProg -> String -> IO ()
test tpqn q t cp fn = do
  let mf = genMidiFile tpqn q (map fst cp) t
      f  = serialise mf
      l  = cast $ length f
  case !(newBuffer l) of
    Nothing => putStrLn "error generating buffer"
    Just b  => do
      setData b f
      putStrLn $ case !(writeBufferToFile fn b l) of
        Left (err, n) => "Error after writing \{show n} bytes: \{show err}"
        Right ()      => "written to " ++ fn

-- TODO: The maths here is incorrect
testDefs : Swing -> Tune -> (Nat -> ChordProg) -> String -> IO ()
testDefs s t cp = test 480 q (playIt s t) (playIt s $ cp q)
  where q : Nat
        q = case s of
          Straight => 16
          Swung    => 12
          Shuffled => 6

test251 : String -> IO ()
test251 fn = do
  t <- sampleIO $ twoFivePrior 16
  testDefs Straight t twoFive fn

test12bb : String -> IO ()
test12bb fn = testDefs Straight !(sampleIO $ nBarBlues 12) twelveBarBlues fn

test12bbf : String -> IO ()
test12bbf fn = testDefs Swung !(sampleIO $ nBarBlues 24) twelveBarBluesFancy fn
