import AFTD.Prelude

/-!
# op75_subset

Topic: np_completeness   Node: 54dad840a017

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

A real target belongs to the subset sums of a list when it can be obtained recursively by either omitting or including the first weight.
-/

def op75_subset : List ℝ → ℝ → Prop
  | [], t => t = 0
  | a :: as, t => op75_subset as t ∨ op75_subset as (t-a)
