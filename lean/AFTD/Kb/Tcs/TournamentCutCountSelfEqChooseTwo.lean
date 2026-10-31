import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_cut_count_self_eq_choose_two

Topic: graphs   Node: e3829f85bd03

Provenance: helper lemma. arXiv:2610.40521 Lemma 2 proof

In any tournament T on vertex set Fin n and for any subset S of vertices, the number of directed edges with both endpoints in S equals Nat.choose S.card 2.
-/

open Classical in
/-- In a tournament, the number of directed edges within any vertex subset S is (|S| choose 2). -/
lemma tournament_cut_count_self_eq_choose_two (n : ℕ) (T : Digraph (Fin n))
    (hT : digraph_is_tournament T) (S : Finset (Fin n)) :
    digraph_cut_count T S S = Nat.choose S.card 2 := by
  have h_out : digraph_cut_count T S S = ∑ i ∈ S, ∑ j ∈ S, (if T.Adj i j then 1 else 0) := by
    dsimp [digraph_cut_count]
    rw [Finset.card_filter]
    exact Finset.sum_product' S S (fun x y => if T.Adj x y then 1 else 0)
  have h_pair : ∀ i j : Fin n,
      ((if T.Adj i j then 1 else 0) + (if T.Adj j i then 1 else 0)) = if i = j then 0 else 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [hT.1 i]
    · rw [if_neg hij]
      have h_adj := hT.2 i j hij
      by_cases h : T.Adj i j
      · simp [h, (h_adj.1 h)]
      · simp [h, (h_adj.not.1 h)]
  have h_row : ∀ i ∈ S, ∑ j ∈ S, (if i = j then 0 else 1) = S.card - 1 := by
    intro i hi
    have h_add : (∑ j ∈ S, (if i = j then 0 else 1)) + (∑ j ∈ S, (if i = j then 1 else 0)) =
        ∑ j ∈ S, 1 := by
      rw [← Finset.sum_add_distrib]
      congr 1
      ext j
      split_ifs <;> rfl
    have h_one : (∑ j ∈ S, (if i = j then 1 else 0)) = 1 := by
      rw [Finset.sum_ite_eq S i (fun _ => (1 : ℕ))]
      simp [hi]
    have h_tot : (∑ j ∈ S, (1 : ℕ)) = S.card := by
      simp
    omega
  have h_double : 2 * digraph_cut_count T S S = S.card * (S.card - 1) := by
    rw [h_out, two_mul]
    have hcomm : (∑ i ∈ S, ∑ j ∈ S, (if T.Adj i j then 1 else 0)) =
        ∑ i ∈ S, ∑ j ∈ S, (if T.Adj j i then 1 else 0) := by
      rw [Finset.sum_comm]
    nth_rw 2 [hcomm]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    simp_rw [h_pair]
    have h_sum_row : (∑ i ∈ S, ∑ j ∈ S, (if i = j then 0 else 1)) = ∑ i ∈ S, (S.card - 1) := by
      apply Finset.sum_congr rfl
      exact h_row
    rw [h_sum_row]
    simp
  rw [Nat.choose_two_right]
  omega
