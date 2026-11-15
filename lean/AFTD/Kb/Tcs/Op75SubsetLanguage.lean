import AFTD.Prelude
import AFTD.Kb.Tcs.Op75SubsetEncoding
import AFTD.Kb.Tcs.Op75Subset

/-!
# op75_subset_language

Topic: np_completeness   Node: db9b0d76f9a6

Provenance: helper lemma. OP-75 one-pass subset-sum construction, arXiv:2610.06092; binary source encoding for a machine-level reduction.

The language of canonical binary words encoding a finite list of nonnegative integer weights and a target that is a subset sum of the list.
-/

def op75_subset_language : Language Bool := {w | ∃ as : List ℕ, ∃ t : ℕ, op75_subset_encoding as t = w ∧ op75_subset (as.map fun a => (a : ℝ)) (t : ℝ)}
