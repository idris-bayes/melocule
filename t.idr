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


Note : Type
Note = Fin 12
ppNote : Note -> String
ppNote x = index x ["C", "C♯", "D", "D♯", "E", "F", "F♯", "G", "G♯", "A", "B♭", "B"]

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

data Chord = MkChord Note        -- Root
                     ChordQual
                     (List Int)  -- Extensions
%runElab derive "Chord" [Generic, Eq]
Show Chord where
  show (MkChord k q es) = ppNote k ++ " \{show q} \{show es}"

data ScaleQual = MajorS
               | MinorS
               | NeutralS
data MajorScale = Ionian
                | PentatonicMaj
                | BluesMaj
data MinorScale = HarmonicMin
                | MelodicMin
                | PentatonicMin
                | BluesMin
data NeutralScale = WholeTone
                  | Chromatic
data Scale = Maj MajorScale
           | Min MinorScale
           | Neu NeutralScale
%runElab derive "MajorScale"   [Generic, Eq]
%runElab derive "MinorScale"   [Generic, Eq]
%runElab derive "NeutralScale" [Generic, Eq]
%runElab derive "Scale"        [Generic, Eq]
Show MajorScale where
  show Ionian        = "Scale"
  show BluesMaj      = "Blues"
  show PentatonicMaj = "Pentatonic"
Show MinorScale where
  show HarmonicMin   = "Harmonic"
  show MelodicMin    = "Melodic"
  show BluesMin      = "Blues"
  show PentatonicMin = "Pentatonic"
Show NeutralScale where
  show Chromatic = "Chromatic"
  show WholeTone = "Whole Tone"
Show Scale where
  show (Maj s) = show s
  show (Min s) = show s
  show (Neu s) = show s


majScales : Vect ? MajorScale
majScales = [ Ionian
            , BluesMaj
            , PentatonicMaj ]

minScales : Vect ? MinorScale
minScales = [ HarmonicMin
            , MelodicMin
            , BluesMin
            , PentatonicMin ]

neuScales : Vect ? NeutralScale
neuScales = [ Chromatic
            , WholeTone ]


majScaleToNotes : MajorScale -> (n : Nat ** Vect n Note)
majScaleToNotes Ionian        = depLen [root, second, majThird, fourth, fifth, majSixth, majSeventh]
majScaleToNotes BluesMaj      = depLen [root, second, minThird, majThird, fifth, majSixth]
majScaleToNotes PentatonicMaj = depLen [root, second,           majThird, fifth, majSixth]

minScaleToNotes : MinorScale -> (n : Nat ** Vect n Note)
minScaleToNotes HarmonicMin   = depLen [root, second, minThird, fourth, fifth, minSixth, majSeventh]
minScaleToNotes MelodicMin    = depLen [root, second, minThird, fourth, fifth, majSixth, majSeventh]
minScaleToNotes BluesMin      = depLen [root, minThird, fourth, dimFifth, fifth, minSeventh]
minScaleToNotes PentatonicMin = depLen [root, minThird, fourth,           fifth, minSeventh]

neuScaleToNotes : NeutralScale -> (n : Nat ** Vect n Note)
neuScaleToNotes Chromatic = depLen $ fromList $ map (restrict 11) $ [0..11]
neuScaleToNotes WholeTone = depLen [0, 2, 4, 6, 8, 10]

scaleToNotes : Scale -> (n : Nat ** Vect n Note)
scaleToNotes (Maj s) = majScaleToNotes s
scaleToNotes (Min s) = minScaleToNotes s
scaleToNotes (Neu s) = neuScaleToNotes s


data Setting = MkSet Chord Scale
%runElab derive "Setting" [Generic, Eq]
Show Setting where
  show (MkSet c s) = show c ++ " " ++ show s


cMaj, gMaj, dMin : Chord
cMaj = MkChord c Major []
gMaj = MkChord g Major []
dMin = MkChord d Minor []

twoFive : Vect ? Chord
twoFive = [dMin, gMaj, cMaj]

partial
uniformScale : MonadSample m => (n : Nat) -> Scale -> m (Vect n Note)
uniformScale n s = do
  let (S l ** ns) = scaleToNotes s
  replicateM n $ uniformD ns

uniformDurations : MonadSample m => (n : Nat) -> m (Vect n Duration)
uniformDurations n = pure $ replicate n (16 `div` n)

partial
genBar : MonadSample m => (n : Nat) -> Scale -> m (Tune n)
genBar n s = do
  notes <- uniformScale n s
  durs <- uniformDurations n
  pure $ zip notes durs

genScale : {n : Nat} -> MonadSample m => Vect n s -> Vect n Double -> m s
genScale ss ps = pure $ index !(categorical ps) ss

genMajorScale : MonadSample m => Vect 3 Double -> m Scale
genMajorScale ps = Maj <$> genScale majScales ps

genMinorScale : MonadSample m => Vect 4 Double -> m Scale
genMinorScale ps = Min <$> genScale minScales ps

genNeutralScale : MonadSample m => Vect 2 Double -> m Scale
genNeutralScale ps = Neu <$> genScale neuScales ps

transpose : Note -> Tune n -> Tune n
transpose n = map (mapFst (+ n))

partial
twoFivePrior : MonadSample m => Nat -> m (Tune ?)
twoFivePrior n = do
  sTwo  <- genMinorScale [0.125, 0.125, 0.25, 0.5]
  sFive <- genMajorScale [1/6, 1/3, 1/2]
  sOne  <- genMajorScale [1/12, 1/12, 5/6]

  trace ("\D Minor \{show sTwo}, G Major \{show sFive}, C Major \{show sOne}") $ pure ()

  tuneTwo  <- genBar n sTwo
  tuneFive <- genBar n sFive
  tuneOne  <- genBar n sOne

  pure $ (transpose second tuneTwo) ++ (transpose fifth tuneFive) ++ tuneOne

ppTune : Tune n -> IO ()
ppTune = printLn . map (mapFst ppNote)

-- TODO: handle duration
dur2dT : Int -> Duration -> Int
dur2dT tpqn d = cast d * (tpqn `div` 4)

noteToMidiCode : (Note, Duration) -> Vect 2 TrkEvent
noteToMidiCode (n, d) = [ TE 0               $ MidiEvt $ MkChMsg 0 $ NoteOn  n' 64
                        , TE (dur2dT tpqn d) $ MidiEvt $ MkChMsg 0 $ NoteOff n' 64 ]
  where n' : Int
        n' = 60 + cast (finToNat n)
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
  tune <- sampleIO $ twoFivePrior n
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
