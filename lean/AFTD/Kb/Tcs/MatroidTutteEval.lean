import AFTD.Prelude

/-!
# matroid_tutte_eval

Topic: combinatorics   Node: 473fe090cd16

Provenance: formalization of a published result. Source: arXiv:2610.27706, Eq. (3)

The real-valued evaluation of the Tutte polynomial `matroid_tutte_eval M x y : ℝ` of a finite matroid M with instance [M.Finite] at real numbers x and y, defined as the sum over all subsets A of the ground set in M.ground_finite.toFinset.powerset of (x - 1) ^ (M.eRank.toNat - (M.eRk (A : Set α)).toNat) * (y - 1) ^ (A.card - (M.eRk (A : Set α)).toNat).
-/

/-- Evaluation of the Tutte polynomial of a finite matroid at real parameters (x, y). -/
noncomputable def matroid_tutte_eval {α : Type*} (M : Matroid α) [M.Finite] (x y : ℝ) : ℝ := ∑ A ∈ M.ground_finite.toFinset.powerset,
    (x - 1) ^ (M.eRank.toNat - (M.eRk (A : Set α)).toNat) *
    (y - 1) ^ (A.card - (M.eRk (A : Set α)).toNat)
