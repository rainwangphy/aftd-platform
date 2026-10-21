import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidTutteEval

/-!
# matroid_tau

Topic: combinatorics   Node: 1e114be06f2f

Provenance: formalization of a published result. Source: arXiv:2610.27706, Section 2

The real-valued evaluation `matroid_tau M : ℝ` of the Tutte polynomial of a finite matroid M with instance [M.Finite], defined as `matroid_tutte_eval M 1 1`.
-/

/-- The real-valued evaluation of the Tutte polynomial of a matroid at (1, 1). -/
noncomputable def matroid_tau {α : Type*} (M : Matroid α) [M.Finite] : ℝ := matroid_tutte_eval M 1 1
