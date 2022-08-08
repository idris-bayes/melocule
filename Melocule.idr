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

||| Represents a melody or melody fragment (with n notes).
Tune : Type
Tune = List (Note, Duration)

public export
Jingle : Type
Jingle = Tune

||| Mnemonics for notes in the key of C.
c, cs, d, ds, e, f, fs, g, gs, a, bb, b : Note
c  = 0; cs = 1; d  = 2;  ds = 3
e  = 4; f  = 5; fs = 6;  g  = 7
gs = 8; a  = 9; bb = 10; b = 11

||| Mnemonics for intervals in arbitrary scales.
root, flatSecond, second, minThird, majThird, fourth, dimFifth, fifth, minSixth, majSixth, minSeventh, majSeventh : Note
root     = 0; flatSecond = 1; second     = 2; minThird    = 3
majThird = 4; fourth     = 5; dimFifth   = 6; fifth       = 7
minSixth = 8; majSixth   = 9; minSeventh = 10; majSeventh = 11
tritone = dimFifth
augFifth = minSixth

||| Chord qualities.
data ChordQual = Major
               | Minor
               | Dominant
%runElab derive "ChordQual" [Generic, Eq]
Show ChordQual where
  show Major    = "Major"
  show Minor    = "Minor"
  show Dominant = "Dominant"

data Chord = MkChord Note         -- Root
                     ChordQual
                     (List1 Note)  -- List of notes in chord
%runElab derive "Chord" [Generic, Eq]
Show Chord where
  show (MkChord k q ns) = ppNote k ++ " \{show q} \{show ns}"

ChordProg = List Chord

||| Add a chord extension.
extend : Chord -> Note -> Chord
extend (MkChord k q ns) n = MkChord k q (snoc ns $ n+k)

(.major), (.minor), (.dom) : Note -> Chord
(.major) n = MkChord n Major    (map (+n) $ c:::[e,  g])
(.minor) n = MkChord n Minor    (map (+n) $ c:::[ds, g])
(.dom)   n = MkChord n Dominant (map (+n) $ c:::[e,  g])

(.add7) : Chord -> Chord
(.add7) c@(MkChord _ Major _)    = extend c majSeventh
(.add7) c@(MkChord _ Minor _)    = extend c minSeventh
(.add7) c@(MkChord _ Dominant _) = extend c minSeventh

cM7 = c.major.add7
dm7 = d.minor.add7
fM7 = f.major.add7
gd7 = g.dom.add7

twoFive : ChordProg
twoFive = [dm7, gd7, cM7]




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
  pure $ case last' $ takeWhile (\x => fst x < n)
       $ toList
       $ scanl (\(acc, l),e=>(acc+e, snoc l e)) (0, Prelude.Nil) ns of
    Nothing       => [n]
    Just (l, ns') => snoc ns' $ n `minus` l

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

harmonise : ChordProg -> List (Tune) -> Tune
harmonise cs ts = concat $ zipWith (\(MkChord c _ _) => transpose c) cs ts

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

twelveBarBluesProg : ChordProg
twelveBarBluesProg =
  [ cM7, cM7, cM7, cM7
  , fM7, fM7, cM7, cM7
  , gd7, gd7, cM7, cM7 ]

twelveBarBlues : MonadSample m => m Jingle
twelveBarBlues = do
  ts <- replicateM 12 $ genBar 12 $ the (Scale MajorS) Blues
  ?bdy

ppTune : Tune -> IO ()
ppTune = printLn . map (mapFst ppNote)

-- TODO: handle duration
dur2dT : Int -> Duration -> Int
dur2dT tpqn d = cast d * (tpqn `div` 4)

immediately : TrkEvent -> TrkEvent
immediately (TE _ e) = TE 0 e

midiPlayNote : Channel -> Note -> Duration -> List TrkEvent
midiPlayNote c n d = [ TE 0               $ MidiEvt $ MkChMsg 0 $ NoteOn  (cast n) 64
                   , TE (dur2dT tpqn d) $ MidiEvt $ MkChMsg 0 $ NoteOff (cast n) 64 ]
  where tpqn : Int
        tpqn = 480

noteToMidiCode : (Note, Duration) -> List TrkEvent
noteToMidiCode (n, d) = midiPlayNote 1 (n + 60) d

notesToMidiCodes : Tune -> List TrkEvent
notesToMidiCodes = concat . map noteToMidiCode

||| Converts a series of notes to be played into a single chord
||| This prevents cascading delta-times.
parallel : List1 (List TrkEvent) -> List (List TrkEvent)
parallel (t:::ts) = transpose $ t :: map (map immediately) ts

-- hacky
chordToMidiCodes : Chord -> List TrkEvent
chordToMidiCodes (MkChord _ _ ns) = concat $ parallel $ map (\n => toList $ midiPlayNote 2 (n + 48) 16) ns

midiTrk : List TrkEvent -> Chunk
midiTrk ns = Track $ ns ++ [TE 1 $ MetaEvt $ EndOfTrack]

genMidiFile : Int -> List Chord -> Tune -> MidiFile
genMidiFile tpqn cs t = [ Header 1 2 tpqn
                        , midiTrk $ notesToMidiCodes t
                        , midiTrk $ concat $ map chordToMidiCodes cs ]

setData : Buffer -> List Int -> IO ()
setData b is = sequence_ $ zipWith (setByte b) [0 .. cast (length is) - 1] is

partial
test : Tune -> ChordProg -> String -> Nat -> IO ()
test t cp fn n = do
  let mf = genMidiFile 480 (toList cp) t
      f  = serialise mf
      l  = cast $ length f
  case !(newBuffer l) of
    Nothing => putStrLn "error generating buffer"
    Just b  => do
      setData b f
      putStrLn $ case !(writeBufferToFile fn b l) of
        Left (err, n) => "Error after writing \{show n} bytes: \{show err}"
        Right ()      => "written to " ++ fn

test251 : String -> IO ()
test251 fn = do
  t <- sampleIO $ twoFivePrior 16
  test t twoFive fn 16

test12bb : String -> IO ()
test12bb fn = do
  tbb <- sampleIO twelveBarBlues

  test tbb twelveBarBluesProg fn 16
