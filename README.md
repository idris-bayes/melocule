# melocule
Probabilistic music composition in Idris2

melocule is a probabilistic composition library/program written in Idris2, based on monad-bayes.
It is intended to be used to model jazz improvisation.

## Installing
This has `libgsl` and `idris2-pack` as hard dependencies.
`lilypond` is required if you wish to have PDFs generated from the makefile.
Without this, the examples will error on `make pdfs`, but you can still call `make midi`.

To use melocule, simply add the following to your `pack.toml`:
```
[custom.all.melocule]
type   = "github"
url    = "https://github.com/idris-bayes/melocule"
commit = "latest:main"
ipkg   = "melocule.ipkg"
```
You can then add `import Melocule` to an Idris2 file and get hacking!

## Running
The Makefile provides the following targets:

- `clean`: cleans the build and output directories.
- `dependencies`: installs the Idris2 dependencies.
- `melocule`: builds melocule as a program (currently an alias for `dependencies`).
- `twofive`: executes the 2-5-1 example.
- `blues`: executes the blues example.
- `fmttm`: executes the Fly Me To The Moon example.
- `midi`: generates MIDI files for all examples.
- `pdfs`: generates PDFs of all MIDI files in the `out/` directory.
- `generate`: generates all MIDI and PDF files.
- `all`: builds melocule, and generates the MIDI and PDF files for every example.

Your generated MIDI and PDF files are contained in the `out/` directory.

## Structure
melocule generates notes according to music theoretical rules.
The idea here is if we know which notes sound good in a given context, we can simply select from these, and compose them (much like molecules; hence the pun).

### Theory
The `Theory.idr` file contains information about music theory, namely a representation of notes/tunes, chords, scales, and rhythm.

#### Chords
Chords are defined by a quality (major, minor or dominant currently), and the list of notes inside them.
This list should be in ascending order, with the root of the chord coming first. Inversions will be handled afterwards.
Chords (and their extensions) can easily be defined using an eDSL:
```
cm7 = C .minor.add7
cM7 = C .major.add7
bbd7add9 = Bb .dom.add7.add9
```
The `.add7` extension (and similar for `.add6`, `.add9` etc.) will determine which seventh to use based on the chord quality.

Chord progressions can be defined, which are a list of chords paired with durations for each.
The function `mkChordProg` can be used to assist this; it takes a list of chords and a Nat `n`, and sets the duration of each chord to `n`.
We provide a simple 251, the 12 bar blues (with simple and fancy variants), and Fly Me To The Moon. All are in C Major.

#### Scales
Scales are defined by a quality also, here only major or minor.
They are represented as offsets from a root note, so once scales are generated they must be transposed to the desired key.

#### Rhythm
Rhythm is currently represented as a stream of time intervals, quantised to 6 quanta per 16th note.
From testing, this seems to allow for enough variety to encode many different types of modern jazz rhythms.
By default we include straight, swung and shuffled 16th notes, and a simple Son Clave (to demonstrate non-traditional western rhythms).
We can then provide functions that act on any rhythm in general; namely, `getBeat`, which groups the first `n~Geo(p)` beats together into one.
This allows us to inject more rhythmic variety over a predefined rhythm.

### Generation
`Generation.idr` handles the actual generation of music from the theory. The primary functions are `genScale` and `genBar`.

`genScale` takes a scale quality and a list of probabilities.
These probabilities are the assigned likelihood of picking each scale from the list of scales for that quality.
The length of this list *must* equal the number of defined scales, otherwise you will get a runtime error.
The function will return your chosen scale.

`genBar` takes a rhythm, a maximum number of notes for the bar, a scale, and the underlying chord.
It will then alter the rhythm by combining notes (as discussed earlier), and pick a melody from the given scale and chord information.
The generated rhythm is first split into fragments arbitrarily.
Then, each melody fragment by choosing to either pick random notes from the scale, walk the scale, or arpeggiate the chord (all with equal likelihood).
The fragments are then combined together and placed above the rhythm, forming a whole bar.

### Output
This file deals with converting a generated Tune into MIDI.
There's not much theoretically interesting here, and from a programmers perspective only the `writeTune` and `writeTuneDefault` functions are likely to be of importance.
`writeTune` takes the MIDI ticks-per-quarter-note value (effectively a quantisation amount), a *melocule duration* quantisation amount (currently assumed to be 16), a tune, a chord progression, and a filename.
It will then generate a MIDI file according to these parameters and write it to the filename.
`writeTuneDefault` takes a tune, chord progression and filename, and sets the tpqn to 480 and the quantisation to 16.
The primary difference is the chord progression is passed without specifying `n` in mkChordProg.

### Utils
This file is simply for programming utils that really should be elsewhere.

## Examples
The Examples directory has some example programs that generate music.
They can be run through the makefile, and will produce output in the `out/` directory.

### 251
The TwoFive example is the most low-level, and focuses on scale generation.
It picks a scale to play over each chord in a 251, and creates a tune from this.

### Blues
The blues example focuses on reusing one generation function over multiple chord progressions.
There are two writing functions, one for the simple chord progression, one for the fancy one.

### Fly Me To The Moon
This is a(n incomplete) test of generating a full song, with a head and solo.
