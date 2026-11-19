import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Majorizes

/-!
# op2046_majorization_forces_top_edge

Topic: quantum_mechanics   Node: b790a3d294ce

Provenance: helper lemma. Singleton-subset consequence of the majorization definition for OP-2046.

If a normalized finite vector majorizes another under the subset-sum definition, every normalized coordinate of the second is bounded above by some normalized coordinate of the first.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_majorization_forces_top_edge (n : ℕ) (x y : Fin n → ℝ)
  (h : op2046_majorizes n x y) : ∀ j : Fin n, ∃ i : Fin n,
  y j / (∑ k, y k) ≤ x i / (∑ k, x k) := by
  intro j
  obtain ⟨S, hS, hineq⟩ := h.2.2 {j}
  have hcard : S.card = 1 := by simpa using hS
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  exact ⟨i, by simpa using hineq⟩
