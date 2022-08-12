module Music.Theory

import Data.List
import Data.List1
import Data.Stream
import Generics.Derive

%language ElabReflection

||| Represents a chord degree. Ostensibly this is Fin 12, but using Nat allows a simpler way
||| of representing notes that go outside of an octave.
public export
Note : Type
Note = Nat

||| Pretty prints a note.
export
ppNote : Note -> String
ppNote x = index (restrict 11 $ cast x) ["C", "C♯", "D", "D♯", "E", "F", "F♯", "G", "G♯", "A", "B♭", "B"]

||| Duration of a note, represented as number of semiquavers/sixteenth notes in the interval.
public export
Duration : Type
Duration = Nat  -- TODO: use rep that supports e.g. triplets

||| A sequence of tys with attachced durations.
public export
Sequence : Type -> Type
Sequence ty = List (ty, Duration)

||| Represents a melody or melody fragment (with n notes).
public export
Tune : Type
Tune = Sequence Note

||| Mnemonics for notes in the key of C.
export
C, Cs, D, Ds, Eb, E, F, Fs, G, Gs, A, Bb, B : Note
C  = 0; Cs = 1; D  = 2;  Ds = 3; Eb = 3
E  = 4; F  = 5; Fs = 6;  G  = 7
Gs = 8; A  = 9; Bb = 10; B = 11

||| Mnemonics for intervals in arbitrary scales.
export
root, flatSecond, second, minThird, majThird, fourth, dimFifth, fifth, minSixth, majSixth, minSeventh, majSeventh : Note
root     = 0; flatSecond = 1; second     = 2; minThird    = 3
majThird = 4; fourth     = 5; dimFifth   = 6; fifth       = 7
minSixth = 8; majSixth   = 9; minSeventh = 10; majSeventh = 11

tritone = dimFifth
augFifth = minSixth

minNinth = 12 + flatSecond
majNinth = 12 + second

||| Encodes the quality of a chord.
public export
data ChordQual = Major
               | Dominant
               | Minor
--%runElab derive "ChordQual" [Generic, Eq]
export
Show ChordQual where
  show Major    = "Major"
  show Dominant = "Dominant"
  show Minor    = "Minor"

||| Chords, represented as a root note, Quality, and list of notes in the chord.
||| Representation may change as the root is included in the list.
public export
data Chord = MkChord Note          -- Root
                     ChordQual
                     (List1 Note)  -- List of notes in chord
--%runElab derive "Chord" [Generic, Eq]
export
Show Chord where
  show (MkChord k q ns) = ppNote k ++ " \{show q} \{show ns}"

||| Represents a chord progression.
public export
ChordProg : Type
ChordProg = Sequence Chord

||| Generate a ChordProg given a list of chords and a number of notes per bar
||| (i.e. the quantisation amount).
export
mkChordProg : List Chord -> Nat -> ChordProg
mkChordProg cs n = map (\c => (c, n)) cs


||| Add a chord extension.
export
extend : Chord -> Note -> Chord
extend (MkChord k q ns) n = MkChord k q (snoc ns $ n+k)

export
(.major), (.minor), (.dom) : Note -> Chord
(.major) n = MkChord n Major    (map (+n) $ C:::[E,  G])
(.dom)   n = MkChord n Dominant (map (+n) $ C:::[E,  G])
(.minor) n = MkChord n Minor    (map (+n) $ C:::[Eb, G])

||| Extend a chord with its sixth degree
export
(.add6) : Chord -> Chord
(.add6) c@(MkChord _ Major _)    = extend c majSixth
(.add6) c@(MkChord _ Dominant _) = extend c majSixth
(.add6) c@(MkChord _ Minor _)    = extend c minSixth

||| Extend a chord with its seventh degree
export
(.b7), (.s7), (.add7) : Chord -> Chord
(.b7) c = extend c minSeventh
(.s7) c = extend c majSeventh
(.add7) c@(MkChord _ Major _)    = extend c majSeventh
(.add7) c@(MkChord _ Dominant _) = extend c minSeventh
(.add7) c@(MkChord _ Minor _)    = extend c minSeventh

||| Extend a chord with its ninth degree
export
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

||| Some sample Chord Progressions. The input natural is the number of quantised
||| notes per bar.
export
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


||| Represents the quality of a scale. Either Major or Minor.
public export
data ScaleQual = MajorS
               | MinorS
export
Show ScaleQual where
  show MajorS   = "Major"
  show MinorS   = "Minor"

||| Represents a scale as a dependent pair of quality and scale "shape".
public export
data Scale : ScaleQual -> Type where
  Chromatic  : Scale q
  WholeTone  : Scale q
  Ionian     : Scale MajorS
  Harmonic   : Scale q
  Melodic    : Scale MinorS
  Pentatonic : Scale q
  Blues      : Scale q
export
{q : ScaleQual} -> Show (Scale q) where
  show Ionian     = "Major"
  show Harmonic   = "Harmonic \{show q}"
  show Melodic    = "Melodic Minor"
  show Chromatic  = "Chromatic"
  show WholeTone  = "Whole Tone"
  show Pentatonic = "\{show q} Pentatonic"
  show Blues      = "\{show q} Blues"

||| List of all the major scales.
public export
majScales : List (Scale MajorS)
majScales = [ Ionian
             , Blues
             , Pentatonic
             , Harmonic]
||| List of all the minor scales.
public export
minScales : List (Scale MinorS)
minScales = [ Harmonic
             , Melodic
             , Blues
             , Pentatonic ]
||| List of all the "neutral" scales, those being scales with no discernible
||| quality.
public export
neuScales : List (Scale q)
neuScales = [ Chromatic
             , WholeTone ]

||| Gets the number of scales in a quality. Useful for making types align.
public export
nScales : ScaleQual -> Nat
nScales MajorS = length majScales
nScales MinorS = length minScales

||| Gets the scales for a given quality.
export
getScales : (q : ScaleQual) -> List (Scale q)
getScales MajorS = majScales
getScales MinorS = minScales

||| Gets the notes from a given scale.
export
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


||| Represents a rhythm as an infinite stream of durations.
public export
Rhythm : Type
Rhythm = Stream Duration

||| Represents a rhythm of straight 16th notes, quantised to 6 quanta per 16th note.
||| Equivalent to a swing of 50% in a DAW.
export
straight16s : Rhythm
straight16s = repeat 6

||| Represents a rhythm of swung 16th notes, quantised to 6 quanta per 16th note.
||| Equivalent to a swing of 66% in a DAW.
export
swung16s : Rhythm
swung16s = cycle [8, 4]

||| Represents a rhythm of shuffled 16th notes, quantised to 6 quanta per 16th note.
||| Equivalent to a swing of 75% in a DAW.
export
shuffle16s : Rhythm
shuffle16s = cycle [9, 3]
