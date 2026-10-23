import AFTD.Prelude
import AFTD.Kb.Tcs.QuinticDecoder
import AFTD.Kb.Tcs.Bit

/-!
# quinticDecoder_eval_parity

Topic: circuits   Node: e56f8bec3561

Provenance: formalization of a published result. Source: arXiv:2610.19174 Theorem 3.2.1

For any integer z ∈ {-1, 0, 1} and any Boolean b, the formal polynomial quinticDecoder evaluated at 2 * (z : ℝ) + bit b equals bit b.
-/

/-- Evaluation of the quintic decoder on points of the form 2z + b for z ∈ {-1, 0, 1}. -/
theorem quinticDecoder_eval_parity (z : ℤ) (hz : z = -1 ∨ z = 0 ∨ z = 1) (b : Bool) :
    quinticDecoder.eval (2 * (z : ℝ) + bit b) = bit b := by
  rcases hz with rfl | rfl | rfl <;> cases b <;> simp [quinticDecoder, bit] <;> norm_num
