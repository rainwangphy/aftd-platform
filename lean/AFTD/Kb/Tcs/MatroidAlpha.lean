import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidTutteEval

/-!
# matroid_alpha

Topic: combinatorics   Node: 5b1cc27d3945

Provenance: formalization of a published result. Source: arXiv:2610.27706, Section 2

The real-valued evaluation `matroid_alpha M : ℝ` of the Tutte polynomial of a finite matroid M with instance [M.Finite], defined as `matroid_tutte_eval M 2 0`.
-/

/-- The real-valued evaluation of the Tutte polynomial of a matroid at (2, 0). -/
noncomputable def matroid_alpha {α : Type*} (M : Matroid α) [M.Finite] : ℝ := matroid_tutte_eval M 2 0
