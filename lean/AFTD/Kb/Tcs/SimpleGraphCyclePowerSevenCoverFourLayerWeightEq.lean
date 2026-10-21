import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenLayerWeightLe

/-!
# simple_graph_cycle_power_seven_cover_four_layer_weight_eq

Topic: combinatorics   Node: e6c482f7f8e6

Provenance: helper lemma. helper for RT-1 (k = 7 case of OP-205, arXiv:2610.15635): the step hW_eq inside the proof of simple_graph_cycle_power_seven_cover_four_tight, exposed for one layer

In any cover of C_n^7 (n ≥ 22) by 4 equivalence subgraphs, every layer has weight exactly n: the sum over i of 2·[i ~ i+7] + [i ~ i+6] + [i ~ i+4] in that layer equals n.
-/

theorem simple_graph_cycle_power_seven_cover_four_layer_weight_eq (n : ℕ) [NeZero n] (hn : 22 ≤ n)
    (c : Fin 4 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 7).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n 7).Adj u v → ∃ s, c s u = c s v) (s : Fin 4) :
    ∑ i : ZMod n, (2 * (if c s i = c s (i + 7) then 1 else 0) + (if c s i = c s (i + 6) then 1 else 0)
      + (if c s i = c s (i + 4) then 1 else 0)) = n := by
  open BigOperators Finset in
  have hadj7 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 7) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨7, by decide, by decide, by push_cast; rfl⟩
  have hadj6 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 6) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨6, by decide, by decide, by push_cast; rfl⟩
  have hadj4 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 4) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨4, by decide, by decide, by push_cast; rfl⟩
  have hcov7 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 7) := fun i => hcov i (i + 7) (hadj7 i)
  have hcov6 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 6) := fun i => hcov i (i + 6) (hadj6 i)
  have hcov4 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 4) := fun i => hcov i (i + 4) (hadj4 i)

  let W : Fin 4 → ℕ := fun s =>
    ∑ i : ZMod n, (2 * (if c s i = c s (i + 7) then 1 else 0) + (if c s i = c s (i + 6) then 1 else 0)
      + (if c s i = c s (i + 4) then 1 else 0))
  have hW_le : ∀ s : Fin 4, W s ≤ n := fun s =>
    simple_graph_cycle_power_seven_layer_weight_le n hn (c s) (hc s)

  have hsum_le : ∑ s : Fin 4, W s ≤ 4 * n := by
    have h := sum_le_card_nsmul (univ : Finset (Fin 4)) W n (fun s _ => hW_le s)
    simp only [card_univ, Fintype.card_fin] at h
    rw [Nat.nsmul_eq_mul] at h
    exact h

  let N7 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 7) then 1 else 0
  let N6 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 6) then 1 else 0
  let N4 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 4) then 1 else 0

  have hN7_ge : ∀ i : ZMod n, 1 ≤ N7 i := by
    intro i
    rcases hcov7 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 7) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have hN6_ge : ∀ i : ZMod n, 1 ≤ N6 i := by
    intro i
    rcases hcov6 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 6) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have hN4_ge : ∀ i : ZMod n, 1 ≤ N4 i := by
    intro i
    rcases hcov4 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 4) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have h_term_ge : ∀ i : ZMod n, 4 ≤ 2 * N7 i + N6 i + N4 i := fun i => by
    have := hN7_ge i
    have := hN6_ge i
    have := hN4_ge i
    omega

  have hsum_comm : ∑ s : Fin 4, W s = ∑ i : ZMod n, (2 * N7 i + N6 i + N4 i) := by
    dsimp [W, N7, N6, N4]
    rw [sum_comm]
    congr 1
    ext i
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum]

  have hsum_ge : 4 * n ≤ ∑ s : Fin 4, W s := by
    rw [hsum_comm]
    have h := card_nsmul_le_sum (univ : Finset (ZMod n)) (fun i => 2 * N7 i + N6 i + N4 i) 4 (fun i _ => h_term_ge i)
    have hc : card (univ : Finset (ZMod n)) = n := ZMod.card n
    rw [hc, Nat.nsmul_eq_mul] at h
    omega

  have hsum_eq : ∑ s : Fin 4, W s = 4 * n := by omega
  have hsum_term_eq : ∑ i : ZMod n, (2 * N7 i + N6 i + N4 i) = 4 * n := by omega

  have hW_eq : ∀ s : Fin 4, W s = n := by
    intro s
    have hsum_const : ∑ _s : Fin 4, n = 4 * n := by
      simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    have hle' : ∀ s ∈ (univ : Finset (Fin 4)), W s ≤ (fun _ => n) s := fun s _ => hW_le s
    by_contra hne
    have hlt : W s < n := lt_of_le_of_ne (hW_le s) hne
    have : ∑ x : Fin 4, W x < ∑ _x : Fin 4, n := Finset.sum_lt_sum hle' ⟨s, mem_univ s, hlt⟩
    omega

  exact hW_eq s
