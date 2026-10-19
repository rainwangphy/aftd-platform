import AFTD.Prelude
import AFTD.Kb.Tcs.CampbellHowardConditions

/-!
# not_campbell_howard_conditions_zero

Topic: quantum   Node: fc3006047800

Provenance: helper lemma. arXiv:2610.09341 Table 1

The zero matrices do not satisfy the Campbell-Howard conditions because condition K3 requires an odd triple overlap of the logical rows, whereas the zero matrix has triple overlap 0.
-/

/-- The zero matrices do not satisfy the Campbell-Howard conditions. -/
theorem not_campbell_howard_conditions_zero (s n : ℕ) :
    ¬ campbell_howard_conditions (0 : Matrix (Fin 3) (Fin n) (ZMod 2)) (0 : Matrix (Fin s) (Fin n) (ZMod 2)) := by
  intro h
  have h3 := h.2.2.1
  simp at h3
