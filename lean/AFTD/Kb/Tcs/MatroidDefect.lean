import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidTau
import AFTD.Kb.Tcs.MatroidAlphaStar
import AFTD.Kb.Tcs.MatroidAlpha

/-!
# matroid_defect

Topic: combinatorics   Node: ef4047247f57

Provenance: formalization of a published result. Source: arXiv:2610.27706, Section 2, Eq. (4)

The real-valued multiplicative defect `matroid_defect M : ℝ` of a finite matroid M with instance [M.Finite], defined as `matroid_alpha M * matroid_alpha_star M - (matroid_tau M) ^ 2` in terms of the invariants `matroid_alpha`, `matroid_alpha_star`, and `matroid_tau`.
-/

/-- The real-valued multiplicative defect of a matroid: alpha times alpha star minus tau squared. -/
noncomputable def matroid_defect {α : Type*} (M : Matroid α) [M.Finite] : ℝ := matroid_alpha M * matroid_alpha_star M - (matroid_tau M) ^ 2
