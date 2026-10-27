import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicLayerWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverCardBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_cycle_power_dyadic_cover_tight_long_edges

Topic: combinatorics   Node: bc7f3a038253

Provenance: helper lemma. Uniform saturation step for OP-205 / RT-1 following arXiv:2610.15635. This is the arbitrary-bandwidth analogue of the exact-edge part of the proved k=3 and k=7 tight-cover helpers; no research advance is claimed.

In an m+1-layer equivalence cover at dyadic bandwidth, every endpoint-distance edge and every other positively weighted dyadic long edge is covered by exactly one layer.
-/

theorem simple_graph_cycle_power_dyadic_cover_tight_long_edges
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v) :
    (∀ i : ZMod n, ∃! s : Fin (m + 1),
      c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n))) ∧
    ∀ j : ℕ, 1 ≤ j → j < m → ∀ i : ZMod n,
      ∃! s : Fin (m + 1),
        c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) := by
  classical
  let d0 : ZMod n := ((2 ^ m - 1 : ℕ) : ZMod n)
  let D : ℕ → ZMod n := fun j => ((2 ^ m - 2 ^ j : ℕ) : ZMod n)
  let I0 : Fin (m + 1) → ZMod n → ℕ := fun s i => if c s i = c s (i + d0) then 1 else 0
  let Ij : Fin (m + 1) → ℕ → ZMod n → ℕ := fun s j i => if c s i = c s (i + D j) then 1 else 0
  let W : Fin (m + 1) → ℕ := fun s => ∑ i : ZMod n, (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i))
  let N0 : ZMod n → ℕ := fun i => ∑ s : Fin (m+1), I0 s i
  let Nj : ℕ → ZMod n → ℕ := fun j i => ∑ s : Fin (m+1), Ij s j i
  let J : Finset ℕ := (Finset.range m).filter (fun j => j ≠ 0)
  have hk_lt : 2 ^ m - 1 < n := by
    have hge : 1 ≤ 2 ^ m - 1 := by
      have h2 : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    omega
  have hadj0 : ∀ i : ZMod n,
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj i (i + d0) := by
    intro i
    rw [show d0 = ((2 ^ m - 1 : ℕ) : ZMod n) from rfl]
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt n (2 ^ m - 1) hk_lt]
    refine ⟨((2 ^ m - 1 : ℕ) : ℤ), ?_, ?_, ?_⟩
    · have hge : 0 < 2 ^ m - 1 := by
        have h2 : 2 ≤ 2 ^ m := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
      omega
    · rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ ((2 ^ m - 1 : ℕ) : ℤ))]
    · push_cast; ring
  have hadjJ : ∀ (j : ℕ), j < m → ∀ i : ZMod n,
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj i (i + D j) := by
    intro j hj i
    rw [show D j = ((2 ^ m - 2 ^ j : ℕ) : ZMod n) from rfl]
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt n (2 ^ m - 1) hk_lt]
    refine ⟨((2 ^ m - 2 ^ j : ℕ) : ℤ), ?_, ?_, ?_⟩
    · have hpos : 0 < 2 ^ m - 2 ^ j := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)
      omega
    · have hle : 2 ^ m - 2 ^ j ≤ 2 ^ m - 1 := by
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      have hnn : (0:ℤ) ≤ ((2 ^ m - 2 ^ j : ℕ) : ℤ) := by positivity
      rw [abs_of_nonneg hnn]
      exact_mod_cast hle
    · push_cast; ring
  have hcov0 : ∀ i : ZMod n, ∃ s : Fin (m+1), c s i = c s (i + d0) :=
    fun i => hcov i (i + d0) (hadj0 i)
  have hcovJ : ∀ j ∈ J, ∀ i : ZMod n, ∃ s : Fin (m+1), c s i = c s (i + D j) := by
    intro j hj i
    have hjm : j < m := by
      have hh : j ∈ (Finset.range m).filter (fun j => j ≠ 0) := hj
      rw [Finset.mem_filter, Finset.mem_range] at hh
      exact hh.1
    exact hcov i (i + D j) (hadjJ j hjm i)
  have hW_le : ∀ s : Fin (m+1), W s ≤ n := fun s =>
    simple_graph_cycle_power_dyadic_layer_weight_le m n hm hn (c s) (hc s)
  have hsum_le : ∑ s : Fin (m+1), W s ≤ (m+1) * n := by
    have h := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin (m+1)))) => hW_le s)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at h
    exact h
  have hT_split : ∀ i : ZMod n,
      (∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i)))
      = 2 * N0 i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Nj j i) := by
    intro i
    rw [Finset.sum_add_distrib]
    rw [show (∑ s : Fin (m+1), 2 * I0 s i) = 2 * N0 i by rw [Finset.mul_sum]]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_ite_irrel]
    by_cases h : j = 0
    · simp [h]
    · simp only [if_neg h]; rfl
  have hJcard : J.card = m - 1 := by
    have hmem : 0 ∈ Finset.range m := by rw [Finset.mem_range]; omega
    simp only [J, Finset.filter_ne', Finset.card_erase_of_mem hmem, Finset.card_range]
  have hN0_ge : ∀ i, 1 ≤ N0 i := by
    intro i
    rcases hcov0 i with ⟨s, hs⟩
    have h := Finset.single_le_sum (f := fun x => I0 x i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    rwa [show I0 s i = 1 by simp [I0, hs]] at h
  have hNJ_ge : ∀ j ∈ J, ∀ i, 1 ≤ Nj j i := by
    intro j hj i
    rcases hcovJ j hj i with ⟨s, hs⟩
    have h := Finset.single_le_sum (f := fun x => Ij x j i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    rwa [show Ij s j i = 1 by simp [Ij, hs]] at h
  have hJsum : ∀ i,
      (∑ j ∈ Finset.range m, (if j = 0 then 0 else Nj j i)) = ∑ j ∈ J, Nj j i := by
    intro i
    change (∑ j ∈ Finset.range m, (if j = 0 then 0 else Nj j i))
      = ∑ j ∈ (Finset.range m).filter (fun j => j ≠ 0), Nj j i
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j = 0 <;> simp [h]
  have hT_ge : ∀ i, m + 1 ≤ ∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i)) := by
    intro i
    rw [hT_split i, hJsum i]
    have hle : J.card ≤ ∑ j ∈ J, Nj j i := by
      have h := Finset.sum_le_sum (fun j hj => hNJ_ge j hj i)
      simpa using h
    have hn0 := hN0_ge i
    omega
  have hsumT : ∑ i : ZMod n, (∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i)))
      = ∑ s : Fin (m+1), W s := by
    simp only [W]
    rw [Finset.sum_comm]
  have hsum_ge : (m+1) * n ≤ ∑ s : Fin (m+1), W s := by
    rw [← hsumT]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (ZMod n))) => hT_ge i)
    have hc : ∑ _i : ZMod n, (m+1) = (m+1) * n := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, Nat.nsmul_eq_mul, Nat.mul_comm]
    rw [hc] at h
    exact h
  have hsum_eq : ∑ s : Fin (m+1), W s = (m+1) * n := le_antisymm hsum_le hsum_ge
  have hW_eq : ∀ s : Fin (m+1), W s = n := by
    intro s
    by_contra hne
    have hlt : W s < n := lt_of_le_of_ne (hW_le s) hne
    have hconst : ∑ _x : Fin (m+1), n = (m+1) * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    have hstrict : ∑ x : Fin (m+1), W x < ∑ _x : Fin (m+1), n :=
      Finset.sum_lt_sum (fun x _ => hW_le x) ⟨s, Finset.mem_univ s, hlt⟩
    rw [hconst, hsum_eq] at hstrict
    exact lt_irrefl _ hstrict
  have hT_eq : ∀ i : ZMod n, (∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i))) = m + 1 := by
    intro i
    by_contra hne
    have hlt : m + 1 < (∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i))) :=
      lt_of_le_of_ne (hT_ge i) (Ne.symm hne)
    have hconst : ∑ _i : ZMod n, (m+1) = (m+1) * n := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, Nat.nsmul_eq_mul, Nat.mul_comm]
    have hstrict : ∑ i : ZMod n, (m+1) < ∑ i : ZMod n, (∑ s : Fin (m+1), (2 * I0 s i + ∑ j ∈ Finset.range m, (if j = 0 then 0 else Ij s j i))) :=
      Finset.sum_lt_sum (fun i _ => hT_ge i) ⟨i, Finset.mem_univ i, hlt⟩
    rw [hconst, hsumT, hsum_eq] at hstrict
    exact lt_irrefl _ hstrict
  have hN0_eq : ∀ i, N0 i = 1 := by
    intro i
    have hT := hT_eq i
    rw [hT_split i, hJsum i] at hT
    have hle : J.card ≤ ∑ j ∈ J, Nj j i := by
      have h := Finset.sum_le_sum (fun j hj => hNJ_ge j hj i)
      simpa using h
    have hn0 := hN0_ge i
    have hJc := hJcard
    omega
  have hNj_eq : ∀ j ∈ J, ∀ i, Nj j i = 1 := by
    intro j hj i
    have hT := hT_eq i
    rw [hT_split i, hJsum i] at hT
    have hn0 := hN0_eq i
    have hsum : ∑ x ∈ J, Nj x i = m - 1 := by
      have hJc := hJcard
      omega
    have hsub : ∑ x ∈ J, (Nj x i - 1) = 0 := by
      have h1 : ∑ x ∈ J, (Nj x i - 1) + ∑ x ∈ J, (1:ℕ) = ∑ x ∈ J, Nj x i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        have := hNJ_ge x hx i
        omega
      have hc1 : ∑ x ∈ J, (1:ℕ) = J.card := by simp
      have hJc := hJcard
      omega
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (s := J) (f := fun x => Nj x i - 1)
      (fun x hx => by have := hNJ_ge x hx i; omega)).mp hsub
    have := hzero j hj
    have := hNJ_ge j hj i
    omega
  have h_exists_unique : ∀ (P : Fin (m+1) → Prop) [DecidablePred P],
      (∑ s : Fin (m+1), (if P s then 1 else 0)) = 1 → ∃! s, P s := by
    intro P _ h
    have hcard : (Finset.univ.filter P).card = 1 := by
      have h1 : (∑ s : Fin (m+1), if P s then 1 else 0 : ℕ) = (Finset.univ.filter P).card := by
        rw [Finset.card_filter]
      rwa [← h1]
    rw [Finset.card_eq_one] at hcard
    rcases hcard with ⟨s, hs⟩
    use s
    have hp : ∀ x, P x ↔ x = s := by
      intro x
      have := Finset.ext_iff.mp hs x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at this
      exact this
    exact ⟨(hp s).mpr rfl, fun x hx => (hp x).mp hx⟩
  refine ⟨fun i => ?_, fun j hj1 hjm i => ?_⟩
  · have := hN0_eq i
    refine h_exists_unique (fun s => c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n))) ?_
    simpa [N0, I0, d0] using this
  · have hjJ : j ∈ J := by
      change j ∈ (Finset.range m).filter (fun j => j ≠ 0)
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjm, by omega⟩
    have := hNj_eq j hjJ i
    refine h_exists_unique (fun s => c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n))) ?_
    simpa [Nj, Ij, D] using this
