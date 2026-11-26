import AFTD.Prelude

/-!
# qutrit_cyclic_tetrahedron_weights

Topic: quantum   Node: 78e6ead71b80

Provenance: helper lemma. OP-2299 cyclic equality-face decomposition, exact coefficient relations 41122.

The cyclic equality-face Bell-weight relations and the PPT coefficient bound give nonnegative weights for the four line states.
-/

theorem qutrit_cyclic_tetrahedron_weights (p : Fin 3 → Fin 3 → ℝ)
    (hpos : ∀ v : Fin 3, 0 ≤ p 2 v)
    (hupper : 3*p 1 0 ≤ ∑ u : Fin 3, ∑ v : Fin 3, p u v)
    (h11 : p 1 1 = 0) (h12 : p 1 2 = 0)
    (hw : p 1 0 = p 2 0+p 2 1+p 2 2)
    (h01 : p 0 0-p 2 0 = p 0 1-p 2 2)
    (h02 : p 0 0-p 2 0 = p 0 2-p 2 1) :
    ∃ c : ℝ, 0 ≤ c ∧ (∀ v : Fin 3, 0 ≤ p 2 v) ∧
      p 0 0 = c+p 2 0 ∧ p 0 1 = c+p 2 2 ∧ p 0 2 = c+p 2 1 ∧
      p 1 0 = p 2 0+p 2 1+p 2 2 := by
  simp only [Fin.sum_univ_three] at hupper
  refine ⟨p 0 0-p 2 0, ?_, hpos, ?_, ?_, ?_, hw⟩
  · linarith
  · ring
  · linarith
  · linarith
