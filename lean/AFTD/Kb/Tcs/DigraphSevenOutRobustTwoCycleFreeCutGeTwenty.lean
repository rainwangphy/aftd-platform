import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.SortedSevenRobustPeelingCapacity
import AFTD.Kb.Tcs.DigraphSevenOutRobustCutThresholds

/-!
# digraph_seven_out_robust_two_cycle_free_cut_ge_twenty

Topic: graphs   Node: 6cc450ed6e05

Provenance: helper lemma. Robust peeling step for the minimum-counterexample campaign route to OP-110; experiment 12598 exhausts the degree arithmetic.

A set of at least seven vertices in a digraph of minimum outdegree seven, containing no two disjoint directed cycles, has at least twenty arcs leaving it if the stated robust two-cycle criterion is available on its subsets.
-/

set_option maxHeartbeats 3000000
private theorem in833_superlevel_count_arithmetic
    (n1 n2 n3 n4 n5 n6 : ℕ)
    (h12 : n2 ≤ n1) (h23 : n3 ≤ n2) (h34 : n4 ≤ n3)
    (h45 : n5 ≤ n4) (h56 : n6 ≤ n5)
    (h0 : 1 ≤ n6 ∨ 3 ≤ n5)
    (h1 : 2 ≤ n5 ∨ 4 ≤ n4)
    (h2 : 3 ≤ n4 ∨ 5 ≤ n3)
    (h3 : 4 ≤ n3 ∨ 6 ≤ n2)
    (h4 : 5 ≤ n2 ∨ 7 ≤ n1) :
    20 ≤ n1+n2+n3+n4+n5+n6 := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> omega

private lemma in833_layer_cake {α : Type} [DecidableEq α] (B : Finset α) (d : α → ℕ) :
    (∑ k ∈ Finset.range 6, (B.filter fun v => k+1 ≤ d v).card) ≤ ∑ v ∈ B, d v := by
  classical
  have hswap : (∑ k ∈ Finset.range 6, (B.filter fun v => k+1 ≤ d v).card) =
      ∑ v ∈ B, ((Finset.range 6).filter fun k => k+1 ≤ d v).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_le_sum
  intro v hv
  have hsub : (Finset.range 6).filter (fun k => k+1 ≤ d v) ⊆ Finset.range (d v) := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    exact Finset.mem_range.mpr (by omega)
  have h := Finset.card_le_card hsub
  simpa only [Finset.card_range] using h

theorem digraph_seven_out_robust_two_cycle_free_cut_ge_twenty
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (B : Finset α) (hB : 7 ≤ B.card)
    (hdeg : ∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α,
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    20 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
  classical
  let d : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card
  let n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ d v).card
  have hnmono : ∀ i j : ℕ, i ≤ j → n j ≤ n i := by
    intro i j hij
    apply Finset.card_le_card
    intro v hv
    have hh := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hh.1, le_trans hij hh.2⟩
  have ht := digraph_seven_out_robust_cut_thresholds α D B hB hdeg hrobust hno
  change (1 ≤ n 6 ∨ 3 ≤ n 5) ∧ (2 ≤ n 5 ∨ 4 ≤ n 4) ∧
    (3 ≤ n 4 ∨ 5 ≤ n 3) ∧ (4 ≤ n 3 ∨ 6 ≤ n 2) ∧ (5 ≤ n 2 ∨ 7 ≤ n 1) at ht
  rcases ht with ⟨h0,h1,h2,h3,h4⟩
  have hn := in833_superlevel_count_arithmetic (n 1) (n 2) (n 3) (n 4) (n 5) (n 6)
    (hnmono 1 2 (by omega)) (hnmono 2 3 (by omega)) (hnmono 3 4 (by omega))
    (hnmono 4 5 (by omega)) (hnmono 5 6 (by omega)) h0 h1 h2 h3 h4
  have hl : (∑ k ∈ Finset.range 6, n (k+1)) ≤ ∑ v ∈ B, d v := in833_layer_cake B d
  have hs : (∑ k ∈ Finset.range 6, n (k+1)) = n 1+n 2+n 3+n 4+n 5+n 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rw [hs] at hl
  change 20 ≤ ∑ v ∈ B, d v
  omega
