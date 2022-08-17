module Melocule.Generation

import Control.Monad.Bayes.Interface
import Control.Monad.Bayes.Sampler
import Data.List1
import Data.Stream
import Syntax.WithProof

import Melocule.Theory
import Melocule.Util


||| Direction for a meldoy fragment to proceed in.
public export
data Dir = Up
         | Down
export
dirs : Vect ? Dir
dirs = [Up, Down]

||| Melody Fragments used for constructing tunes.
public export
data MelodyFrag = ||| Distribute notes uniformly through a scale.
                  Uniform
                | ||| Arpeggiate the underlying chord.
                  Arpeggio
                | ||| Walk through the scale.
                  Walk
export
mfrags : List MelodyFrag
mfrags = [Uniform, Arpeggio, Walk]

export
catIndex : MonadSample m => (weights : List Double) -> (categories : List s) ->
  (0 ford : length weights === length categories) =>
  m s
catIndex ps ss = do
  let ps' := Vect.fromList ps
      ss' := Vect.fromList ss
  pure $
    index !(categorical $ rewrite sym ford in ps') $ ss'

export
uniformScale : MonadSample m => {q : ScaleQual} -> Nat -> Scale q -> m (List Note)
uniformScale n s = assert_total $ do
  let ns = scaleToNotes q s
      (S n ** prf) := @@(length ns)
      | _ => pure []
  replicateM n $ uniformD
               $ replace {p = \u => Vect u Nat} prf
               $ fromList ns

export
endless : forall elem'. List elem' -> Stream elem'
endless xs = endlessAux xs
  where
    endlessAux : List elem' -> Stream elem'
    endlessAux [] = endlessAux xs
    endlessAux (y :: ys) = y :: endlessAux ys


export
runDir : Dir -> Nat -> List a -> List a
runDir Up   n = take n . endless
runDir Down n = reverse . take n . endless

export
scaleDir : {q : ScaleQual} -> Scale q -> Dir -> (n : Nat) -> List Nat
scaleDir s d n = runDir d n $ scaleToNotes q s

export
arpeggiate : MonadSample m => Nat -> Chord -> m (List Note)
arpeggiate n (MkChord _ ns) = do
  d <- uniformD dirs
  let ns' := runDir d n $ toList ns
  pure ns'

export
walk : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> m (List Nat)
walk n s = do
  dir <- uniformD dirs
  pure $ scaleDir s dir n

export
genMelodyFrag : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> Chord -> m (List Note)
genMelodyFrag n s c = do
  case !(uniformD $ fromList' [] mfrags) of
    Uniform  => uniformScale n s
    Arpeggio => arpeggiate n c
    Walk     => walk n s

getBeat : MonadSample m => Double -> Rhythm -> m (Duration, Rhythm)
getBeat p r = do
  n <- geometric p
  pure $ (sum $ toList $ Stream.take n r, Stream.drop n r)

export
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

export
genMelody : MonadSample m => {q : ScaleQual} -> (n : Nat) -> Scale q -> Chord -> m (List Note)
genMelody n s c = do
  ls <- fragment n 0.2
  nss <- sequence $ map (\l => genMelodyFrag l s c) ls
  pure $ concat nss

partial export
genBar : MonadSample m => {q : ScaleQual} -> Rhythm -> Nat -> Scale q -> Chord -> m Tune
genBar r n s c = do
  durs1 <- getBeats (n`div`2) r
  durs2 <- getBeats (n`div`2) r
  let durs = durs1 ++ durs2
      l    = length durs
  notes <- genMelody l s c
  pure $ zip notes durs

export
genScale : MonadSample m => (q : ScaleQual) -> (weights : List Double) ->
  (0 ford : length weights = nScales q) =>
  m (Scale q)
genScale MajorS ps = catIndex ps majScales
genScale MinorS ps = catIndex ps minScales

export
transpose : Note -> Tune -> Tune
transpose n = map (mapFst (+ n))

export
requantise : Nat -> Sequence a -> Sequence a
requantise n = map (mapSnd (* n))
