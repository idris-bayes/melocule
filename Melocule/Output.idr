||| Module to handle converting a tune to MIDI data
module Melocule.Output
{-
Future additions:
- Support parallel and sequential composition of tracks a la Euterpea
  would make this module a lot more flexible externally
- Allow alternate tempo information
  Probably involves completely refactoring the quantisation stuff
-}

import Control.Monad.Bayes.Sampler
import Data.Buffer
import Data.Fin
import Data.List
import Data.List1
import Sound.Midi.Types
import Sound.Midi.Serialise
import System.File.Buffer

import Melocule.Theory
import Melocule.Util

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

||| Writes a tune given a specified ticks-per-quarter-note value, a quantisation
||| level, the tune, the chord progression, and a filename.
public export
writeTune : Int -> Nat -> Tune -> ChordProg -> String -> IO ()
test tpqn q t cp fn = do
  let mf = genMidiFile tpqn q (cp.chords) t
      f  = serialise mf
      l  = cast $ length f
  case !(newBuffer l) of
    Nothing => putStrLn "error generating buffer"
    Just b  => do
      setData b f
      putStrLn $ case !(writeBufferToFile fn b l) of
        Left (err, n) => "Error after writing \{show n} bytes: \{show err}"
        Right ()      => "written to " ++ fn

||| Writes a tune, setting some default values for MIDI-specific generation.
public export
writeTuneDefault : Tune -> (Nat -> ChordProg) -> String -> IO ()
writeTuneDefault t cp = writeTune 480 16 t (cp 16)
