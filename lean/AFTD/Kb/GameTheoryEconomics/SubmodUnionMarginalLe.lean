import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submod_union_marginal_le

Topic: fair_division   Node: 733806f0996f

For a monotone submodular set function and S inside T, adding a set U gains at most as much on top of T as on top of S.
-/

/-- For a monotone submodular set function and `S ⊆ T`, adding a set `U` gains at most as much on top of `T` as on top of `S`. -/
theorem submod_union_marginal_le {m : ℕ} (v : Finset (Fin m) → ℝ) (hmono : Monotone v)
    (hsub : is_submodular v) {S T : Finset (Fin m)} (hST : S ⊆ T) (U : Finset (Fin m)) :
    v (T ∪ U) - v T ≤ v (S ∪ U) - v S := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert a U ha ih =>
    rw [Finset.union_insert, Finset.union_insert]
    by_cases haT : a ∈ T ∪ U
    · rw [Finset.insert_eq_of_mem haT]
      have : v (S ∪ U) ≤ v (insert a (S ∪ U)) := hmono (Finset.subset_insert _ _)
      linarith
    · have h := hsub (S ∪ U) (T ∪ U) a (Finset.union_subset_union hST le_rfl) haT
      linarith
