module Melocule

import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Data.Buffer
import Data.List1
import Data.List
import Data.Stream
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
arpeggiate n (MkChord _ ns) = do
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


getBeat : MonadSample m => Double -> Rhythm -> m (Duration, Rhythm)
getBeat p r = do
  n <- geometric p
  pure $ (sum $ toList $ Stream.take n r, Stream.drop n r)

getBeats : MonadSample m => Nat -> Rhythm -> m (List Duration)
getBeats = go 0
  where go : Nat -> Nat -> Rhythm -> m (List Duration)
        go acc n r = case acc >= n of
                       True => pure $ []
                       False => do
                            (d, r') <- getBeat 0.62 r
                            if acc + d > n
                              then pure [minus n acc]
                              else (d ::) <$> go (min n $ acc + d) n r'


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
genBar : MonadSample m => {q : ScaleQual} -> Rhythm -> Nat -> Scale q -> Chord -> m Tune
genBar r n s c = do
  --durs1 <- genRhythm (n`div`2) 0.62
  --durs2 <- genRhythm (n`div`2) 0.62
  durs1 <- getBeats (n`div`2) r
  durs2 <- getBeats (n`div`2) r
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

  tuneTwo  <- genBar straight16s n sTwo dm7
  tuneFive <- genBar straight16s n sFive gd7
  tuneOne  <- genBar straight16s n sOne cM7

  pure $ (transpose second tuneTwo) ++ (transpose fifth tuneFive) ++ tuneOne

nBarBlues : MonadSample m => Nat -> m Tune
nBarBlues n = do
  scale <- bluesOrPenta
  ns <- replicateM n (genBar straight16s 96 scale cd7) -- TODO: take chordprog and change this
  pure $ concat ns
  where bluesOrPenta : m (Scale MajorS)
        bluesOrPenta = uniformD [Blues, Pentatonic]

fmttm : MonadSample m => m Tune
fmttm = do
  let c = the (Scale MajorS) Ionian
      a = the (Scale MinorS) Melodic
  cs <- map concat $ replicateM 5 $ genBar straight16s 96 c cM7
  as <- map (transpose (minus A 12) . concat) $ replicateM 3 $ genBar straight16s 96 a am7
  pure $ cs ++ as

ppTune : Tune -> IO ()
ppTune = printLn . map (mapFst ppNote)

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
chordToMidiCodes tpqn q (MkChord _ ns) = concat
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
testDefs : Tune -> (Nat -> ChordProg) -> String -> IO ()
testDefs t cp = test 480 16 t (cp 16)

test251 : String -> IO ()
test251 fn = do
  t <- sampleIO $ twoFivePrior 96
  testDefs t twoFive fn

test12bb : String -> IO ()
test12bb fn = testDefs !(sampleIO $ nBarBlues 12) twelveBarBlues fn

test12bbf : String -> IO ()
test12bbf fn = testDefs !(sampleIO $ nBarBlues 24) twelveBarBluesFancy fn

testfmttm : String -> IO ()
testfmttm fn = testDefs !(sampleIO fmttm) flyMeToTheMoon fn
