import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# nat_mex_list_not_mem_and_lt

Topic: combinatorial_games   Node: 924cec4426c1

Provenance: helper lemma. step towards spider_eventual_parity_two_three

For a list l of naturals, nat_mex_list l is not a member of l, and every natural number below nat_mex_list l is a member of l.
-/

lemma nat_mex_list_not_mem_and_lt_loop_spec (l : List ℕ) (fuel : ℕ) (n : ℕ) :
    (nat_mex_list.loop l n fuel ∉ l ∧ (∀ k, n ≤ k → k < nat_mex_list.loop l n fuel → k ∈ l)) ∨
    (nat_mex_list.loop l n fuel = n + fuel ∧ (∀ k, n ≤ k → k < n + fuel → k ∈ l)) := by
  induction fuel generalizing n with
  | zero =>
    right
    exact ⟨rfl, fun k h1 h2 => by omega⟩
  | succ fuel ih =>
    have hstep : nat_mex_list.loop l n (fuel + 1) = if n ∈ l then nat_mex_list.loop l (n + 1) fuel else n := rfl
    rw [hstep]
    by_cases hn : n ∈ l
    · rw [if_pos hn]
      rcases ih (n + 1) with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        refine ⟨h1, fun k hk1 hk2 => ?_⟩
        rcases eq_or_lt_of_le hk1 with rfl | hlt
        · exact hn
        · exact h2 k hlt hk2
      · right
        refine ⟨by omega, fun k hk1 hk2 => ?_⟩
        rcases eq_or_lt_of_le hk1 with rfl | hlt
        · exact hn
        · exact h2 k hlt (by omega)
    · rw [if_neg hn]
      left
      exact ⟨hn, fun k hk1 hk2 => by omega⟩

/-- The mex of a finite list of naturals is absent from the list, and every smaller number occurs in it. -/
theorem nat_mex_list_not_mem_and_lt (l : List ℕ) :
    nat_mex_list l ∉ l ∧ ∀ k, k < nat_mex_list l → k ∈ l := by
  change (nat_mex_list.loop l 0 (l.length + 1) ∉ l ∧ ∀ k, k < nat_mex_list.loop l 0 (l.length + 1) → k ∈ l)
  rcases nat_mex_list_not_mem_and_lt_loop_spec l (l.length + 1) 0 with (⟨h1, h2⟩ | ⟨-, h2⟩)
  · exact ⟨h1, fun k hk => h2 k (Nat.zero_le k) hk⟩
  · have hsub : List.range (l.length + 1) ⊆ l := by
      intro x hx
      rw [List.mem_range] at hx
      exact h2 x (Nat.zero_le x) (by omega)
    have hle := List.Nodup.length_le_of_subset List.nodup_range hsub
    rw [List.length_range] at hle
    omega
