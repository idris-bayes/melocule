import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Data.Buffer
import Data.Vect
import Generics.Derive
import Sound.Midi.Types
import Sound.Midi.Serialise
import System.File.Buffer

import Debug.Trace
  
%language ElabReflection


replicateM : Applicative m => (n : Nat) -> m a -> m (Vect n a)
replicateM n xs = sequence $ replicate n xs

depLen : {n : Nat} -> Vect n a -> (n : Nat ** Vect n a)
depLen xs = (n ** xs)


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
Tune : Nat -> Type
Tune n = Vect n (Note, Duration)

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
                     (List Note)  -- List of notes in chord
%runElab derive "Chord" [Generic, Eq]
Show Chord where
  show (MkChord k q es) = ppNote k ++ " \{show q} \{show es}"

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
mfrags : Vect ? MelodyFrag
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

majScales : Vect ? (Scale MajorS)
majScales = [ Ionian
             , Blues
             , Pentatonic ]
minScales : Vect ? (Scale MinorS)
minScales = [ Harmonic
             , Melodic
             , Blues
             , Pentatonic ]
neuScales : Vect ? (Scale q)
neuScales = [ Chromatic
             , WholeTone ]

scaleToNotes : (q : ScaleQual) -> Scale q -> (n : Nat ** Vect n Note)
scaleToNotes q      Chromatic  = depLen $ fromList [0..11]
scaleToNotes q      WholeTone  = depLen [0, 2, 4, 6, 8, 10]
scaleToNotes MajorS Ionian     = depLen [root, second, majThird, fourth, fifth, majSixth, majSeventh]
scaleToNotes MajorS Harmonic   = ?unimpl
scaleToNotes MinorS Harmonic   = depLen [root, second, minThird, fourth, fifth, minSixth, majSeventh]
scaleToNotes MinorS Melodic    = depLen [root, second, minThird, fourth, fifth, majSixth, majSeventh]
scaleToNotes MajorS Pentatonic = depLen [root, second,           majThird, fifth, majSixth]
scaleToNotes MinorS Pentatonic = depLen [root, minThird, fourth,           fifth, minSeventh]
scaleToNotes MajorS Blues      = depLen [root, second, minThird, majThird, fifth, majSixth]
scaleToNotes MinorS Blues      = depLen [root, minThird, fourth, dimFifth, fifth, minSeventh]

cMaj, gMaj, dMin : Chord
cMaj = MkChord c Major []
gMaj = MkChord g Major []
dMin = MkChord d Minor []

twoFive : Vect ? Chord
twoFive = [dMin, gMaj, cMaj]



catIndex : MonadSample m => {n : Nat} -> Vect n Double -> Vect n s -> m s
catIndex ps ss = pure $ index !(categorical ps) ss

partial
uniformScale : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (Vect n Note)
uniformScale n s = do
  let (S l ** ns) = scaleToNotes q s
  replicateM n $ uniformD ns

partial
genMelody : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (Vect n Note)
genMelody n s = do
  case !(uniformD mfrags) of
    Uniform  => uniformScale n s
    Arpeggio => ?unimpl_arp
    Walk     => ?unimpl_walk

||| Generates random durations that add up to n. `p` determines likelihood of
||| shorter durations.
genRhythm : MonadSample m => (n : Nat) -> Double -> m (List Duration)
genRhythm n p = do
  ns <- replicateM n $ geometric p
  pure $ case last' $ takeWhile (\x => fst x < n) $ toList $ scanl (\(acc, l),e=>(acc+e, snoc l e)) (0, Prelude.Nil) ns of
    Nothing       => [n]
    Just (l, ns') => snoc ns' $ n `minus` l

partial
genBar : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (k : Nat ** Tune k)
genBar n s = do
  dursL <- genRhythm n 0.6
  let l     = length dursL
      dursM = toVect l dursL
  notes <- uniformScale l s
  pure $ case dursM of  -- TODO: handle properly
    Nothing   => ?inaccessible_genBar
    Just durs => (l ** zip notes durs)

genScale : MonadSample m => {n : Nat} -> Vect n (Scale q) -> Vect n Double -> m (Scale q)
genScale = flip catIndex

transpose : Note -> Tune n -> Tune n
transpose n = map (mapFst (+ n))

harmonise : Vect n Chord -> Vect n (Tune k) -> Tune $ n * k
harmonise cs ts = concat $ zipWith (\(MkChord c _ _) => transpose c) cs ts

partial
twoFivePrior : MonadSample m => Nat -> m (l : Nat ** Tune l)
twoFivePrior n = do
  sTwo  <- genScale minScales [0.125, 0.125, 0.25, 0.5]
  sFive <- genScale majScales [1/6, 1/3, 1/2]
  sOne  <- genScale majScales [1/12, 1/12, 5/6]

  trace ("\D \{show sTwo}, G \{show sFive}, C \{show sOne}") $ pure ()

  (l2 ** tuneTwo)  <- genBar n sTwo
  (l5 ** tuneFive) <- genBar n sFive
  (l1 ** tuneOne)  <- genBar n sOne
  let l = l2 + l5 + l1

  pure $ ((l2 + l5) + l1 ** ((transpose second tuneTwo) ++ (transpose fifth tuneFive)) ++ tuneOne)

cycleFive : MonadSample m => m (l : Nat ** Tune l)
cycleFive = do
  pure (0**[])


ppTune : Tune n -> IO ()
ppTune = printLn . map (mapFst ppNote)

-- TODO: handle duration
dur2dT : Int -> Duration -> Int
dur2dT tpqn d = cast d * (tpqn `div` 4)

noteToMidiCode : (Note, Duration) -> Vect 2 TrkEvent
noteToMidiCode (n, d) = [ TE 0               $ MidiEvt $ MkChMsg 0 $ NoteOn  n' 64
                        , TE (dur2dT tpqn d) $ MidiEvt $ MkChMsg 0 $ NoteOff n' 64 ]
  where n' : Int
        n' = 60 + cast n
        tpqn : Int
        tpqn = 480

notesToMidiCodes : Tune n -> Vect (n * 2) TrkEvent
notesToMidiCodes = concat . map noteToMidiCode

midiHdr : Fin 3 -> Int -> Chunk
midiHdr fmt tpqn = Header 6 fmt 1 tpqn

midiTrk : Vect m TrkEvent -> Chunk
midiTrk ns = Track 0 $ toList ns ++ [TE 1 $ MetaEvt $ EndOfTrack]

genMidiFile : Tune m -> MidiFile
genMidiFile t = [ midiHdr 1 480
                , midiTrk $ notesToMidiCodes t ]

setData : Buffer -> List Int -> IO ()
setData b is = do
  sequence_ $ zipWith (setByte b) [0 .. cast (length is) - 1] is

partial
test : String -> Nat -> IO ()
test fn n = do
  (_**tune) <- sampleIO $ twoFivePrior n
  let mf = genMidiFile tune
      f  = serialise mf
      l  = cast $ length f
  case !(newBuffer l) of
    Nothing => putStrLn "error generating buffer"
    Just b  => do
      setData b f
      putStrLn $ case !(writeBufferToFile fn b l) of
        Left (err, n) => "Error after writing \{show n} bytes: \{show err}"
        Right ()      => "written to " ++ fn
