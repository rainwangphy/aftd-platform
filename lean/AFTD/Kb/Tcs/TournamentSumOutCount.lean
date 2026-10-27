import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_sum_out_count

Topic: graphs   Node: e6d23975d1b4

Provenance: helper lemma. step towards tournament_arborescence_hadamard_bound

In a tournament T on Fin n, the out-degrees sum to the number of unordered pairs: ∑_i d_i = n(n-1)/2.
-/

/-- In a tournament the out-degrees sum to `n(n-1)/2`, the number of pairs. -/
theorem tournament_sum_out_count (n : ℕ) (T : Digraph (Fin n)) [DecidableRel T.Adj] (hT : digraph_is_tournament T) : ∑ i : Fin n, digraph_out_count T i = n * (n - 1) / 2 := by
  have h_out : ∀ i : Fin n, digraph_out_count T i = ∑ j : Fin n, (if T.Adj i j then 1 else 0) := by
    intro i
    dsimp [digraph_out_count]
    exact Finset.card_filter _ Finset.univ
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
  have h_row : ∀ i : Fin n, ∑ j : Fin n, (if i = j then 0 else 1) = n - 1 := by
    intro i
    have h_add : (∑ j : Fin n, (if i = j then 0 else 1)) + (∑ j : Fin n, (if i = j then 1 else 0)) =
        ∑ j : Fin n, 1 := by
      rw [← Finset.sum_add_distrib]
      congr 1
      ext j
      split_ifs <;> rfl
    have h_one : (∑ j : Fin n, (if i = j then 1 else 0)) = 1 := by
      exact Fintype.sum_ite_eq i (fun _ => 1)
    have h_tot : (∑ j : Fin n, (1 : ℕ)) = n := by
      simp
    omega
  have h_double : 2 * (∑ i : Fin n, digraph_out_count T i) = n * (n - 1) := by
    simp_rw [h_out]
    rw [two_mul]
    have hcomm : (∑ i : Fin n, ∑ j : Fin n, (if T.Adj i j then 1 else 0)) =
        ∑ i : Fin n, ∑ j : Fin n, (if T.Adj j i then 1 else 0) := by
      rw [Finset.sum_comm]
    nth_rw 2 [hcomm]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    simp_rw [h_pair]
    simp_rw [h_row]
    simp
  omega
