import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.SubmodUnionMarginalLe

/-!
# submod_zero_marginals

Topic: fair_division   Node: bcd2365028cd

For a monotone submodular set function, items whose marginal value over X is zero add nothing on top of any superset of X.
-/

/-- Items whose marginal value over `X` is zero add nothing on top of any superset of `X`. -/
theorem submod_zero_marginals {m : ℕ} (v : Finset (Fin m) → ℝ) (hmono : Monotone v)
    (hsub : is_submodular v) {X W : Finset (Fin m)} (hXW : X ⊆ W) (R : Finset (Fin m))
    (hR : ∀ z ∈ R, v (insert z X) ≤ v X) : v (W ∪ R) = v W := by
  have key : v (X ∪ R) ≤ v X := by
    induction R using Finset.induction_on with
    | empty => simp
    | insert a R ha ih =>
      have ih' := ih (fun z hz => hR z (Finset.mem_insert_of_mem hz))
      have haX := hR a (Finset.mem_insert_self a R)
      rw [Finset.union_insert]
      by_cases haXR : a ∈ X ∪ R
      · rw [Finset.insert_eq_of_mem haXR]; exact ih'
      · by_cases haX' : a ∈ X
        · exact absurd (Finset.mem_union_left R haX') haXR
        · have h := hsub X (X ∪ R) a Finset.subset_union_left haXR
          linarith
  have h := submod_union_marginal_le v hmono hsub hXW R
  have hge : v W ≤ v (W ∪ R) := hmono Finset.subset_union_left
  have hge' : v X ≤ v (X ∪ R) := hmono Finset.subset_union_left
  linarith
