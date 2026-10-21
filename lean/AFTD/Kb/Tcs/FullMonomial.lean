import AFTD.Prelude
import AFTD.Kb.Tcs.Bit

/-!
# fullMonomial

Topic: circuits   Node: 77abfc7a0c7b

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.13

The full monomial x_[n] = ∏_{i=1}^n x_i evaluated at a point in {0,1}^n.
-/

/-- The full monomial x_[n] evaluated on a Boolean input. -/
def fullMonomial {n : ℕ} (x : Fin n → Bool) : ℝ := ∏ i : Fin n, bit (x i)
