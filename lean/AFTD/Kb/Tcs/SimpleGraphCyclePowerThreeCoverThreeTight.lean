import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeLayerWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeLayerWeightEqImp
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeAdjIff

/-!
# simple_graph_cycle_power_three_cover_three_tight

Topic: combinatorics   Node: a81a0c9a0f9c

Provenance: helper lemma. Step toward simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd (the k = 3 case of OP-205, arXiv:2610.15635): the double-counting proof found in thread RT-1.

If three equivalence subgraphs (labellings c_0, c_1, c_2 with clique classes) cover C_n^3, n ≥ 10, then every pair at distance 3 and every pair at distance 2 lies in exactly one of them, and in every layer every class contains a pair at distance 3 spanning it.
-/

theorem simple_graph_cycle_power_three_cover_three_tight (n : ℕ) [NeZero n] (hn : 10 ≤ n)
    (c : Fin 3 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 3).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n 3).Adj u v → ∃ s, c s u = c s v) :
    (∀ i, ∃! s, c s i = c s (i + 3)) ∧ (∀ i, ∃! s, c s i = c s (i + 2)) ∧
      ∀ s i, ∃ d : ℕ, d ≤ 3 ∧ c s (i - d) = c s (i - d + 3) ∧ c s (i - d) = c s i := by
  open BigOperators Finset in
  have hadj3 : ∀ i : ZMod n, (simple_graph_cycle_power n 3).Adj i (i + 3) := by
    intro i
    rw [simple_graph_cycle_power_three_adj_iff n hn]
    exact ⟨3, by decide, by decide, by push_cast; rfl⟩
  have hadj2 : ∀ i : ZMod n, (simple_graph_cycle_power n 3).Adj i (i + 2) := by
    intro i
    rw [simple_graph_cycle_power_three_adj_iff n hn]
    exact ⟨2, by decide, by decide, by push_cast; rfl⟩
  have hcov3 : ∀ i : ZMod n, ∃ s : Fin 3, c s i = c s (i + 3) := fun i => hcov i (i + 3) (hadj3 i)
  have hcov2 : ∀ i : ZMod n, ∃ s : Fin 3, c s i = c s (i + 2) := fun i => hcov i (i + 2) (hadj2 i)

  let W : Fin 3 → ℕ := fun s =>
    ∑ i : ZMod n, (2 * (if c s i = c s (i + 3) then 1 else 0) + (if c s i = c s (i + 2) then 1 else 0))
  have hW_le : ∀ s : Fin 3, W s ≤ n := fun s =>
    simple_graph_cycle_power_three_layer_weight_le n hn (c s) (hc s)

  have hsum_le : ∑ s : Fin 3, W s ≤ 3 * n := by
    have h := sum_le_card_nsmul (univ : Finset (Fin 3)) W n (fun s _ => hW_le s)
    simp only [card_univ, Fintype.card_fin] at h
    rw [Nat.nsmul_eq_mul] at h
    exact h

  let N3 : ZMod n → ℕ := fun i => ∑ s : Fin 3, if c s i = c s (i + 3) then 1 else 0
  let N2 : ZMod n → ℕ := fun i => ∑ s : Fin 3, if c s i = c s (i + 2) then 1 else 0

  have hN3_ge : ∀ i : ZMod n, 1 ≤ N3 i := by
    intro i
    rcases hcov3 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 3) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have hN2_ge : ∀ i : ZMod n, 1 ≤ N2 i := by
    intro i
    rcases hcov2 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 2) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have h_term_ge : ∀ i : ZMod n, 3 ≤ 2 * N3 i + N2 i := fun i => by
    have := hN3_ge i
    have := hN2_ge i
    omega

  have hsum_comm : ∑ s : Fin 3, W s = ∑ i : ZMod n, (2 * N3 i + N2 i) := by
    dsimp [W, N3, N2]
    rw [sum_comm]
    congr 1
    ext i
    rw [sum_add_distrib, ← mul_sum]

  have hsum_ge : 3 * n ≤ ∑ s : Fin 3, W s := by
    rw [hsum_comm]
    have h := card_nsmul_le_sum (univ : Finset (ZMod n)) (fun i => 2 * N3 i + N2 i) 3 (fun i _ => h_term_ge i)
    have hc : card (univ : Finset (ZMod n)) = n := ZMod.card n
    rw [hc, Nat.nsmul_eq_mul] at h
    omega

  have hsum_eq : ∑ s : Fin 3, W s = 3 * n := by omega
  have hsum_term_eq : ∑ i : ZMod n, (2 * N3 i + N2 i) = 3 * n := by omega

  have hW_eq : ∀ s : Fin 3, W s = n := by
    intro s
    have hsum_const : ∑ _s : Fin 3, n = 3 * n := by
      simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    have hle' : ∀ s ∈ (univ : Finset (Fin 3)), W s ≤ (fun _ => n) s := fun s _ => hW_le s
    by_contra hne
    have hlt : W s < n := lt_of_le_of_ne (hW_le s) hne
    have : ∑ x : Fin 3, W x < ∑ _x : Fin 3, n := Finset.sum_lt_sum hle' ⟨s, mem_univ s, hlt⟩
    omega

  have h_term_eq : ∀ i : ZMod n, 2 * N3 i + N2 i = 3 := by
    intro i
    have hsum_const : ∑ _i : ZMod n, 3 = 3 * n := by
      have hc : card (univ : Finset (ZMod n)) = n := ZMod.card n
      simp only [sum_const, hc, Nat.nsmul_eq_mul]
      omega
    have hle' : ∀ j ∈ (univ : Finset (ZMod n)), (fun _ => 3) j ≤ 2 * N3 j + N2 j := fun j _ => h_term_ge j
    by_contra hne
    have hlt : 3 < 2 * N3 i + N2 i := lt_of_le_of_ne (h_term_ge i) (Ne.symm hne)
    have : ∑ _x : ZMod n, 3 < ∑ x : ZMod n, (2 * N3 x + N2 x) := Finset.sum_lt_sum hle' ⟨i, mem_univ i, hlt⟩
    omega

  have hN3_eq : ∀ i : ZMod n, N3 i = 1 := by
    intro i
    have := h_term_eq i
    have := hN3_ge i
    have := hN2_ge i
    omega

  have hN2_eq : ∀ i : ZMod n, N2 i = 1 := by
    intro i
    have := h_term_eq i
    have := hN3_ge i
    have := hN2_ge i
    omega

  have h_exists_unique : ∀ (P : Fin 3 → Prop) [DecidablePred P],
      (∑ s : Fin 3, (if P s then 1 else 0)) = 1 → ∃! s, P s := by
    intro P _ h
    have hcard : card (filter P univ) = 1 := by
      have h1 : (∑ s : Fin 3, if P s then 1 else 0 : ℕ) = card (filter P univ) := sum_boole (R := ℕ) P univ
      rwa [← h1]
    rw [card_eq_one] at hcard
    rcases hcard with ⟨s, hs⟩
    use s
    have hp : ∀ x, P x ↔ x = s := by
      intro x
      have := Finset.ext_iff.mp hs x
      simp only [mem_filter, mem_univ, true_and, mem_singleton] at this
      exact this
    exact ⟨(hp s).mpr rfl, fun x hx => (hp x).mp hx⟩

  refine ⟨fun i => h_exists_unique (fun s => c s i = c s (i + 3)) (hN3_eq i),
          fun i => h_exists_unique (fun s => c s i = c s (i + 2)) (hN2_eq i),
          fun s i => ?_⟩
  exact simple_graph_cycle_power_three_layer_weight_eq_imp n hn (c s) (hc s) (hW_eq s) i
