import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicLayerWeightLe

/-!
# simple_graph_cycle_power_dyadic_cover_card_bound

Topic: combinatorics   Node: 6bf9bb2c7e76

Provenance: formalization of a published result. Source: arXiv:2610.15635, Lemma 2.2, specialized to k+1=2^m and the stronger range n>=3k+1. This helper uses the uniform dyadic tree weight proof instead of the paper rank argument. It is a known bound, not a research advance.

For dyadic bandwidth 2^m-1 and n at least three times the bandwidth plus one, every equivalence cover of the cycle power uses at least m+1 layers.
-/

private lemma simple_graph_cycle_power_dyadic_cover_card_bound_vertex
    (m n t : ℕ) [NeZero n] (hm : 1 ≤ m) (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin t → ZMod n → ZMod n)
    (hcover : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v → ∃ s, c s u = c s v)
    (i : ZMod n) :
    m + 1 ≤ ∑ s : Fin t, (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
      ∑ j ∈ Finset.range m, if j = 0 then 0 else (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)) := by
  have hadj : ∀ d : ℕ, 1 ≤ d → d ≤ 2 ^ m - 1 →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj i (i + (d : ZMod n)) := by
    intro d hd1 hd2
    have hlt : 2 ^ m - 1 < n := by omega
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt n (2 ^ m - 1) hlt i]
    refine ⟨(d : ℤ), by omega, ?_, ?_⟩
    · have hd : (0:ℤ) ≤ (d:ℤ) := by omega
      rw [abs_of_nonneg hd]
      exact_mod_cast hd2
    · push_cast; ring
  have ind : ∀ (v : ZMod n), (∃ s, c s i = c s v) →
      1 ≤ ∑ s : Fin t, (if c s i = c s v then 1 else 0) := by
    intro v hex
    obtain ⟨s₀, hs₀⟩ := hex
    have h1 := Finset.single_le_sum (f := fun s : Fin t => if c s i = c s v then 1 else 0)
      (fun s _ => by split <;> omega) (Finset.mem_univ s₀)
    simpa [hs₀] using h1
  have hD1 : 1 ≤ 2 ^ m - 1 := by
    have : 2 ≤ 2 ^ m := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hA1 : 1 ≤ ∑ s : Fin t, (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) :=
    ind _ (hcover _ _ (hadj (2 ^ m - 1) hD1 le_rfl))
  have hB1 : ∀ j ∈ Finset.range m, 1 ≤ ∑ s : Fin t,
      (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have h1 : 1 ≤ 2 ^ m - 2 ^ j := by
      have : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hjlt
      omega
    have h2 : 2 ^ m - 2 ^ j ≤ 2 ^ m - 1 := by
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    exact ind _ (hcover _ _ (hadj _ h1 h2))
  have key : ∀ s : Fin t,
      2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        ∑ j ∈ Finset.range m, (if j = 0 then 0 else (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0))
      = (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        ∑ j ∈ Finset.range m, (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) := by
    intro s
    set A : ℕ := if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0 with hA
    set B : ℕ → ℕ := fun j => if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0 with hB
    have hB0 : B 0 = A := by
      simp [hB, hA]
    have hmem : 0 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    have e1 : ((Finset.range m).erase 0).sum B + B 0 = ∑ j ∈ Finset.range m, B j :=
      Finset.sum_erase_add _ _ hmem
    have e2 : ∑ j ∈ Finset.range m, (if j = 0 then 0 else B j) = ((Finset.range m).erase 0).sum B := by
      have h := Finset.sum_erase_add (s := Finset.range m) (f := fun j => if j = 0 then 0 else B j) hmem
      rw [if_pos rfl, Nat.add_zero] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])
    rw [← e1, e2, hB0]
    omega
  rw [Finset.sum_congr rfl (fun s _ => key s)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range m)]
  have hmle : m ≤ ∑ j ∈ Finset.range m, ∑ s : Fin t,
      (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) := by
    simpa using Finset.sum_le_sum hB1
  omega

theorem simple_graph_cycle_power_dyadic_cover_card_bound
    (m n t : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (hcov : simple_graph_has_equivalence_cover
      (simple_graph_cycle_power n (2 ^ m - 1)) t) :
    m + 1 ≤ t := by
  obtain ⟨c, hclique, hcover⟩ := hcov
  set w : ZMod n → Fin t → ℕ := fun i s =>
    2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
    ∑ j ∈ Finset.range m, if j = 0 then 0 else
      (if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) with hw
  have hW : ∀ s : Fin t, ∑ i : ZMod n, w i s ≤ n := by
    intro s
    have := simple_graph_cycle_power_dyadic_layer_weight_le m n hm hn (c s) (hclique s)
    simpa [hw] using this
  have hV : ∀ i : ZMod n, m + 1 ≤ ∑ s : Fin t, w i s := by
    intro i
    have := simple_graph_cycle_power_dyadic_cover_card_bound_vertex m n t hm hn c hcover i
    simpa [hw] using this
  have hmain : (m + 1) * n ≤ t * n := by
    calc (m + 1) * n = ∑ _i : ZMod n, (m + 1) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, Nat.nsmul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ i : ZMod n, ∑ s : Fin t, w i s := Finset.sum_le_sum (fun i _ => hV i)
      _ = ∑ s : Fin t, ∑ i : ZMod n, w i s := Finset.sum_comm
      _ ≤ ∑ _s : Fin t, n := Finset.sum_le_sum (fun s _ => hW s)
      _ = t * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact Nat.le_of_mul_le_mul_right hmain (NeZero.pos n)
