import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexSplit
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.PrefixSum
import AFTD.Kb.GameTheoryEconomics.IndexSplitSpec

/-!
# index_split_combine_inverse

Topic: general_equilibrium   Node: 5f2e9e2d2a13

Provenance: formalization of a published result. Source: EconCSLib, `index_split_combine_inverse`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`index_split` is a left inverse to `index_combine`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `index_split` is a left inverse to `index_combine`. -/
lemma index_split_combine_inverse (p : Σ i, Fin (card i)) : index_split card (index_combine card p) = p := by
  classical
  cases p with
  | mk i j =>
    let k : Fin (total_card card) := index_combine card ⟨i, j⟩
    have hspec := index_split_spec card k

    have prefix_sum_mono_lt : ∀ {a b : I}, a < b →
        prefix_sum card a + (card a : ℕ) ≤ prefix_sum card b := by
      intro a b hlt
      have h_subset : (Finset.univ.filter (· ≤ a)) ⊆ (Finset.univ.filter (· < b)) := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxU, hxle⟩
        exact Finset.mem_filter.mpr ⟨hxU, lt_of_le_of_lt hxle hlt⟩
      have h_eq_a : (Finset.univ.filter (· ≤ a)).sum (fun j => (card j : ℕ)) =
          (Finset.univ.filter (· < a)).sum (fun j => (card j : ℕ)) + (card a : ℕ) := by
        have h_split : Finset.univ.filter (· ≤ a) =
            Finset.univ.filter (· < a) ∪ {a} := by
          ext j; simp [Finset.mem_filter, le_iff_lt_or_eq, or_comm]
        have h_disj : Disjoint (Finset.univ.filter (· < a)) {a} := by simp
        rw [h_split, Finset.sum_union h_disj]; simp
      have h_le : (Finset.univ.filter (· ≤ a)).sum (fun j => (card j : ℕ)) ≤
          (Finset.univ.filter (· < b)).sum (fun j => (card j : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_subset (by
          intro j _ _; exact Nat.zero_le _)
      simpa [prefix_sum, h_eq_a] using h_le

    have hk_le : prefix_sum card i ≤ k.val := by
      simp [k, index_combine]
    have hk_lt : k.val < prefix_sum card i + (card i : ℕ) := by
      simp [k, index_combine, add_lt_add_iff_left]

    have hnot_lt1 : ¬ (index_split card k).1 < i := by
      intro hlt
      have hmono := prefix_sum_mono_lt hlt
      have : k.val < prefix_sum card i := Nat.lt_of_lt_of_le hspec.2.1 hmono
      exact (not_lt_of_ge hk_le) this
    have hnot_lt2 : ¬ i < (index_split card k).1 := by
      intro hlt
      have hmono := prefix_sum_mono_lt hlt
      have : k.val < prefix_sum card (index_split card k).1 := Nat.lt_of_lt_of_le hk_lt hmono
      exact (not_lt_of_ge hspec.1) this
    have hi : (index_split card k).1 = i :=
      le_antisymm (le_of_not_gt hnot_lt2) (le_of_not_gt hnot_lt1)

    have hj_spec : (index_split card k).2.val = k.val - prefix_sum card (index_split card k).1 := hspec.2.2
    have hj_spec_i : (index_split card k).2.val = k.val - prefix_sum card i := by
      simpa [hi] using hj_spec
    have hj_val : (index_split card k).2.val = j.val := by
      simpa [k, index_combine, Nat.add_sub_cancel_left] using hj_spec_i

    cases hsplit : index_split card k with
    | mk i' j' =>
      have hi' : i' = i := by simpa [hsplit] using hi
      subst hi'
      have hj' : j' = j := by
        apply Fin.ext
        rw [hsplit] at hj_val
        exact hj_val
      simpa [hsplit] using hj'
