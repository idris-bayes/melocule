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
import System.File.Buffer

import Syntax.WithProof

import Debug.Trace

%language ElabReflection


replicateM : Applicative m => (n : Nat) -> m a -> m (List a)
replicateM n xs = sequence $ replicate n xs



||| Represents a chord degree. Ostensibly this is Fin 12, but using Nat allows a simpler way
||| of representing notes that go outside of an octave.
Note : Type
Note = Nat

ppNote : Note -> String
ppNote x = index (restrict 11 $ cast x) ["C", "C♯", "D", "D♯", "E", "F", "F♯", "G", "G♯", "A", "B♭", "B"]

||| Duration of a note, represented as number of semiquavers/sixteenth notes in the interval.
Duration : Type
Duration = Nat  -- TODO: use rep that supports e.g. triplets

||| A sequence of tys with attachced durations.
Sequence : Type -> Type
Sequence ty = List (ty, Duration)

||| Represents a melody or melody fragment (with n notes).
Tune : Type
Tune = Sequence Note

public export
Jingle : Type
Jingle = Tune

||| Mnemonics for notes in the key of C.
C, Cs, D, Ds, E, F, Fs, G, Gs, A, Bb, B : Note
C  = 0; Cs = 1; D  = 2;  Ds = 3
E  = 4; F  = 5; Fs = 6;  G  = 7
Gs = 8; A  = 9; Bb = 10; B = 11

||| Mnemonics for intervals in arbitrary scales.
root, flatSecond, second, minThird, majThird, fourth, dimFifth, fifth, minSixth, majSixth, minSeventh, majSeventh : Note
root     = 0; flatSecond = 1; second     = 2; minThird    = 3
majThird = 4; fourth     = 5; dimFifth   = 6; fifth       = 7
minSixth = 8; majSixth   = 9; minSeventh = 10; majSeventh = 11

tritone = dimFifth
augFifth = minSixth

minNinth = 12 + flatSecond
majNinth = 12 + second

||| Chord qualities.
data ChordQual = Major
               | Dominant
               | Minor
%runElab derive "ChordQual" [Generic, Eq]
Show ChordQual where
  show Major    = "Major"
  show Dominant = "Dominant"
  show Minor    = "Minor"

data Chord = MkChord Note          -- Root
                     ChordQual
                     (List1 Note)  -- List of notes in chord
%runElab derive "Chord" [Generic, Eq]
Show Chord where
  show (MkChord k q ns) = ppNote k ++ " \{show q} \{show ns}"

ChordProg = Sequence Chord
mkChordProg : List Chord -> Nat -> ChordProg
mkChordProg cs n = map (\c => (c, n)) cs


||| Add a chord extension.
extend : Chord -> Note -> Chord
extend (MkChord k q ns) n = MkChord k q (snoc ns $ n+k)

(.major), (.minor), (.dom) : Note -> Chord
(.major) n = MkChord n Major    (map (+n) $ C:::[E,  G])
(.dom)   n = MkChord n Dominant (map (+n) $ C:::[E,  G])
(.minor) n = MkChord n Minor    (map (+n) $ C:::[Ds, G])

(.add6) : Chord -> Chord
(.add6) c@(MkChord _ Major _)    = extend c majSixth
(.add6) c@(MkChord _ Dominant _) = extend c majSixth
(.add6) c@(MkChord _ Minor _)    = extend c minSixth

(.b7), (.s7), (.add7) : Chord -> Chord
(.b7) c = extend c minSeventh
(.s7) c = extend c majSeventh
(.add7) c@(MkChord _ Major _)    = extend c majSeventh
(.add7) c@(MkChord _ Dominant _) = extend c minSeventh
(.add7) c@(MkChord _ Minor _)    = extend c minSeventh

(.b9), (.s9), (.add9) : Chord -> Chord
(.b9) c = extend c minNinth
(.s9) c = extend c majNinth
(.add9) c@(MkChord _ Major _)    = extend c majNinth
(.add9) c@(MkChord _ Dominant _) = extend c majNinth
(.add9) c@(MkChord _ Minor _)    = extend c minNinth

cM6 = C .major.add6
cM7 = C .major.add7
cd7 = C .dom.add7
cd9 = cd7.add9
dm7 = D .minor.add7
fM7 = F .major.add7
fd7 = F .dom.add7
fd9 = fd7.add9
gd7 = G .dom.add7
gd9 = gd7.add9

twoFive, twelveBarBlues, twelveBarBluesFancy : Nat -> ChordProg
twoFive = mkChordProg [dm7, gd7, cM7]

twelveBarBlues = mkChordProg
  [ cd7, cd7, cd7, cd7
  , fd7, fd7, cd7, cd7
  , gd7, fd7, cd7, cd7 ]

twelveBarBluesFancy = mkChordProg
  [ cd7, cd7, cd9, cd7
  , fd7, fd7, cd7, cd7
  , gd7, fd7, cd7, gd9

  , cd7, fd7, cd7, cd7
  , fd7, fd9, cd7, cd7
  , gd7, fd7, cd7, cM6 ]



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

data ScaleQual = MajorS
               | MinorS
Show ScaleQual where
  show MajorS   = "Major"
  show MinorS   = "Minor"

data Scale : ScaleQual -> Type where
  Chromatic  : Scale q
  WholeTone  : Scale q
  Ionian     : Scale MajorS
  Harmonic   : Scale q
  Melodic    : Scale MinorS
  Pentatonic : Scale q
  Blues      : Scale q

MajorScale, MinorScale, NeutralScale : Type
MajorScale = Scale MajorS
MinorScale = Scale MinorS

{q : ScaleQual} -> Show (Scale q) where
  show Ionian     = "Major"
  show Harmonic   = "Harmonic \{show q}"
  show Melodic    = "Melodic Minor"
  show Chromatic  = "Chromatic"
  show WholeTone  = "Whole Tone"
  show Pentatonic = "\{show q} Pentatonic"
  show Blues      = "\{show q} Blues"

majScales : List (Scale MajorS)
majScales = [ Ionian
             , Blues
             , Pentatonic 
             , Harmonic]
minScales : List (Scale MinorS)
minScales = [ Harmonic
             , Melodic
             , Blues
             , Pentatonic ]
neuScales : List (Scale q)
neuScales = [ Chromatic
             , WholeTone ]

nScales : ScaleQual -> Nat
nScales MajorS = length majScales
nScales MinorS = length minScales

getScales : (q : ScaleQual) -> List (Scale q)
getScales MajorS = majScales
getScales MinorS = minScales

scaleToNotes : (q : ScaleQual) -> Scale q -> List Note
scaleToNotes q      Chromatic  = [0..11]
scaleToNotes q      WholeTone  = [0, 2, 4, 6, 8, 10]
scaleToNotes MajorS Ionian     = [root, second, majThird, fourth, fifth, majSixth, majSeventh]
scaleToNotes MajorS Harmonic   = [root, second, majThird, fourth, fifth, minSixth, majSeventh]
scaleToNotes MinorS Harmonic   = [root, second, minThird, fourth, fifth, minSixth, majSeventh]
scaleToNotes MinorS Melodic    = [root, second, minThird, fourth, fifth, majSixth, majSeventh]
scaleToNotes MajorS Pentatonic = [root, second,           majThird, fifth, majSixth]
scaleToNotes MinorS Pentatonic = [root, minThird, fourth,           fifth, minSeventh]
scaleToNotes MajorS Blues      = [root, second, minThird, majThird, fifth, majSixth]
scaleToNotes MinorS Blues      = [root, minThird, fourth, dimFifth, fifth, minSeventh]


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

arpeggiate : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Note)
arpeggiate = do
  --dir <- uniformD dirs
  ?arp

endless : forall elem'. List elem' -> Stream elem'
endless xs = endlessAux xs
  where
    endlessAux : List elem' -> Stream elem'
    endlessAux [] = endlessAux xs
    endlessAux (y :: ys) = y :: endlessAux ys

scaleDir : {q : ScaleQual} -> Scale q -> Dir -> (n : Nat) -> List Nat
scaleDir s Up   n = take n $ endless (scaleToNotes q s)
scaleDir s Down n = reverse $ take n $ endless (scaleToNotes q s)

walk : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Nat)
walk n s = do
  dir <- uniformD dirs
  pure $ scaleDir s dir n


genMelodyFrag : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Note)
genMelodyFrag n s = do
  case !(uniformD $ fromList' [] mfrags) of
    Uniform  => uniformScale n s
    Arpeggio => uniformScale n s --?unimpl_arp
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

genMelody : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Note)
genMelody n s = do
  ls <- fragment n 0.2
  nss <- sequence $ map (\l => genMelodyFrag l s) ls
  pure $ concat nss

||| Generates random durations that add up to n. `p` determines likelihood of
||| shorter durations.
genRhythm : MonadSample m => (n : Nat) -> Double -> m (List Duration)
genRhythm = fragment

partial
genBar : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m Jingle
genBar n s = do
  durs1 <- genRhythm (n`div`2) 0.62
  durs2 <- genRhythm (n`div`2) 0.62
  let durs = durs1 ++ durs2
      l    = length durs
  notes <- genMelody l s
  pure $ zip notes durs

silly : (q : ScaleQual) -> Nat
silly MajorS = length majScales
silly MinorS = length minScales


genScale : MonadSample m => (q : ScaleQual) -> (weights : List Double) ->
  (0 ford : length weights = silly q) =>
  m (Scale q)
genScale MajorS ps = catIndex ps majScales
genScale MinorS ps = catIndex ps minScales

transpose : Note -> Tune -> Tune
transpose n = map (mapFst (+ n))

requantise : Nat -> Sequence a -> Sequence a
requantise n = map (mapSnd (* n))

partial
twoFivePrior : MonadSample m => Nat -> m Jingle
twoFivePrior n = do
  sTwo  <- genScale MinorS [0.125, 0.125, 0.25, 0.5]
  sFive <- genScale MajorS [1/6, 1/3, 1/4, 1/4]
  sOne  <- genScale MajorS [1/12, 1/12, 3/6, 2/6]

  trace ("\D \{show sTwo}, G \{show sFive}, C \{show sOne}") $ pure ()

  tuneTwo  <- genBar n sTwo
  tuneFive <- genBar n sFive
  tuneOne  <- genBar n sOne

  pure $ (transpose second tuneTwo) ++ (transpose fifth tuneFive) ++ tuneOne

cycleFive : MonadSample m => m Jingle
cycleFive = do
  pure []

nBarBlues : MonadSample m => Nat -> m Jingle
nBarBlues n = map concat $ replicateM n (bluesOrPenta >>= genBar 16)
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

-- TODO: handle duration
dur2dT : Int -> Duration -> Int
dur2dT tpqn d = cast d * (tpqn `div` 4)

immediately : TrkEvent -> TrkEvent
immediately (TE _ e) = TE 0 e

midiPlayNote : Int -> Channel -> Note -> Duration -> List TrkEvent
midiPlayNote tpqn c n d = [ TE 0               $ MidiEvt $ MkChMsg 0 $ NoteOn  (cast n) 64
                          , TE (dur2dT tpqn d) $ MidiEvt $ MkChMsg 0 $ NoteOff (cast n) 64 ]

noteToMidiCode : Int -> (Note, Duration) -> List TrkEvent
noteToMidiCode tpqn (n, d) = midiPlayNote tpqn 1 (n + 60) d

notesToMidiCodes : Int -> Tune -> List TrkEvent
notesToMidiCodes tpqn = concat . map (noteToMidiCode tpqn)

||| Converts a series of notes to be played into a single chord
||| This prevents cascading delta-times.
parallel : List1 (List TrkEvent) -> List (List TrkEvent)
parallel (t:::ts) = transpose $ t :: map (map immediately) ts

-- hacky
chordToMidiCodes : Int -> Chord -> List TrkEvent
chordToMidiCodes tpqn (MkChord _ _ ns) = concat
                                       $ parallel
                                       $ map (\n => toList
                                                  $ midiPlayNote tpqn 2 (n + 48) 16)
                                             ns

midiTrk : List TrkEvent -> Chunk
midiTrk ns = Track $ ns ++ [TE 1 $ MetaEvt $ EndOfTrack]

genMidiFile : Int -> List Chord -> Tune -> MidiFile
genMidiFile tpqn cs t = [ Header 1 2 tpqn
                        , midiTrk $ notesToMidiCodes tpqn t
                        , midiTrk $ concat $ map (chordToMidiCodes tpqn) cs ]

setData : Buffer -> List Int -> IO ()
setData b is = sequence_ $ zipWith (setByte b) [0 .. cast (length is) - 1] is

partial
test : Tune -> Int -> ChordProg -> Nat -> String -> IO ()
test t tpqn cp n fn = do
  let mf = genMidiFile 480 (map fst cp) t
      f  = serialise mf
      l  = cast $ length f
  case !(newBuffer l) of
    Nothing => putStrLn "error generating buffer"
    Just b  => do
      setData b f
      putStrLn $ case !(writeBufferToFile fn b l) of
        Left (err, n) => "Error after writing \{show n} bytes: \{show err}"
        Right ()      => "written to " ++ fn

testDefs : Swing -> Tune -> (Nat -> ChordProg) -> String -> IO ()
testDefs s t cp = test (playIt s t) 40 (cp $ 16) 192

test251 : String -> IO ()
test251 fn = do
  t <- sampleIO $ twoFivePrior 16
  testDefs Straight t twoFive fn

test12bb : String -> IO ()
test12bb fn = testDefs Straight !(sampleIO $ nBarBlues 12) twelveBarBlues fn

test12bbf : String -> IO ()
test12bbf fn = testDefs Swung !(sampleIO $ nBarBlues 24) twelveBarBluesFancy fn
