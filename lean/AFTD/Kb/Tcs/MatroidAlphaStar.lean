import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidTutteEval

/-!
# matroid_alpha_star

Topic: combinatorics   Node: 4ba2ad8991e5

Provenance: formalization of a published result. Source: arXiv:2610.27706, Section 2

The real-valued evaluation `matroid_alpha_star M : ℝ` of the Tutte polynomial of a finite matroid M with instance [M.Finite], defined as `matroid_tutte_eval M 0 2`.
-/

/-- The real-valued evaluation of the Tutte polynomial of a matroid at (0, 2). -/
noncomputable def matroid_alpha_star {α : Type*} (M : Matroid α) [M.Finite] : ℝ := matroid_tutte_eval M 0 2
