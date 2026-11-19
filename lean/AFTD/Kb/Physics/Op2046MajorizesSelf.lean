import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Majorizes

/-!
# op2046_majorizes_self

Topic: quantum_mechanics   Node: b5aa24afbc30

Provenance: helper lemma. Definition sanity check for OP-2046.

Every finite real vector with positive sum majorizes itself after normalization.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_majorizes_self (n : ℕ) (x : Fin n → ℝ) (hx : 0 < (∑ i, x i)) : op2046_majorizes n x x := by
  exact ⟨hx, hx, fun T => ⟨T, rfl, le_rfl⟩⟩
