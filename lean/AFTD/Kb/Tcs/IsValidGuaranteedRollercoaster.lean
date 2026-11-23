import AFTD.Prelude
import AFTD.Kb.Tcs.GuaranteedRollercoasterLength
import AFTD.Kb.Tcs.IsKRollercoaster

/-!
# is_valid_guaranteed_rollercoaster

Topic: algorithms   Node: 3fb6e814453b

Provenance: formalization of a published result. Source: arXiv:2611.26297 Sec. 4

A strictly increasing list of indices ans is a valid guaranteed-length k-rollercoaster for a sequence v of length n if its length is at least the guaranteed bound f_k(n) = guaranteed_rollercoaster_length k n, and whenever f_k(n) > 0, the selected subsequence ans.map v is a k-rollercoaster.
-/

/-- An index subsequence is a valid guaranteed-length k-rollercoaster for sequence v. -/
def is_valid_guaranteed_rollercoaster {α : Type*} [LinearOrder α] (k n : ℕ)
    (v : Fin n → α) (ans : List (Fin n)) : Prop :=
  ans.Pairwise (· < ·) ∧
  guaranteed_rollercoaster_length k n ≤ ans.length ∧
  (0 < guaranteed_rollercoaster_length k n → is_k_rollercoaster k (ans.map v))
