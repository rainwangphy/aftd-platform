import AFTD.Prelude
import AFTD.Kb.Tcs.ShiftedDyadicScales
import AFTD.Kb.Tcs.DownScale
import AFTD.Kb.Tcs.PrefixScaleWeight
import AFTD.Kb.Tcs.HarmonicScaleWeight
import AFTD.Kb.Tcs.NatSuccLeTwoPow

/-!
# accumulating_prefix_scales

Topic: online_algorithms   Node: 1a402713e226

Provenance: formalization of a published result. Source: arXiv:2611.17090 Lemma 7 -- Online Transportation via Shifted Geometric Scales

Accumulating prefix edge lengths across dyadic scales (Lemma 7). Let E be a finite set of edges with weights w_e > 0, and for a fixed phase θ ∈ [0, 1), let q_e = down_θ(w_e) and R_θ = {2^{θ+j} : j ∈ ℤ}. For any scale r, let W_θ(r) = ∑_{e ∈ E, q_e ≤ r} w_e, and let H = ∑_{e ∈ E} w_e / q_e. Then for any positive cutoff level B ∈ R_θ and any N ∈ ℕ, the sum of prefix scale weights over the first N dyadic scales descending from B satisfies ∑_{j=0}^{N-1} W_θ(B / 2^j) ≤ H B.
-/

open Classical

lemma accumulating_prefix_scales_ds_eq {θ z : ℝ} (hz : 0 < z) :
    down_scale θ z = 2 ^ (θ + (⌊Real.logb 2 z - θ⌋ : ℝ)) := by
  rw [down_scale]
  simp only [if_neg (not_le.mpr hz)]

lemma accumulating_prefix_scales_ds_le_div_iff {θ : ℝ} {B : ℝ} {m : ℤ}
    (hB : B = 2 ^ (θ + (m:ℝ))) {z : ℝ} (hz : 0 < z) (j : ℕ) :
    down_scale θ z ≤ B / 2 ^ j ↔ (j:ℝ) ≤ (m:ℝ) - (⌊Real.logb 2 z - θ⌋ : ℝ) := by
  rw [accumulating_prefix_scales_ds_eq hz]
  have hdiv : B / 2 ^ j = 2 ^ (θ + (m:ℝ) - (j:ℝ)) := by
    rw [hB, ← Real.rpow_natCast (2:ℝ) j, ← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  rw [hdiv]
  rw [(Real.strictMono_rpow_of_base_gt_one (by norm_num : (1:ℝ) < 2)).le_iff_le]
  constructor <;> intro h <;> linarith

lemma accumulating_prefix_scales_card_filter_le {θ B : ℝ} {m : ℤ}
    (hB : B = 2 ^ (θ + (m:ℝ))) {z : ℝ} (hz : 0 < z) (N : ℕ) :
    ((Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N)).card : ℝ) ≤
      B / down_scale θ z := by
  set k : ℤ := ⌊Real.logb 2 z - θ⌋ with hk
  set d : ℤ := m - k with hd
  have hmem : ∀ j : ℕ, (down_scale θ z ≤ B / 2 ^ j) ↔ (j:ℝ) ≤ (d:ℝ) := by
    intro j
    rw [accumulating_prefix_scales_ds_le_div_iff hB hz j]
    have h1 : (m:ℝ) - (⌊Real.logb 2 z - θ⌋ : ℝ) = (d:ℝ) := by
      rw [hd]; push_cast; ring
    rw [h1]
  have hBq : B / down_scale θ z = 2 ^ (d:ℝ) := by
    rw [accumulating_prefix_scales_ds_eq hz, hB, ← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
    congr 1
    rw [hd, hk]; push_cast; ring
  rw [hBq]
  by_cases hd0 : 0 ≤ d
  · have hdcast : (d.toNat : ℝ) = (d:ℝ) := by
      have h := Int.toNat_of_nonneg hd0
      exact_mod_cast h
    have hsub : Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N) ⊆
        Finset.range (d.toNat + 1) := by
      intro j hj
      rw [Finset.mem_range]
      rw [Finset.mem_filter] at hj
      have hle : (j:ℝ) ≤ (d:ℝ) := (hmem j).mp hj.2
      rw [← hdcast] at hle
      have hle' : j ≤ d.toNat := by exact_mod_cast hle
      omega
    have hcard : (Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N)).card ≤
        d.toNat + 1 := by
      calc (Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N)).card
          ≤ (Finset.range (d.toNat + 1)).card := Finset.card_le_card hsub
        _ = d.toNat + 1 := Finset.card_range _
    have h2 : ((d.toNat + 1 : ℕ) : ℝ) ≤ (2:ℝ) ^ d.toNat := by
      rw [Nat.cast_add, Nat.cast_one]; exact nat_succ_le_two_pow d.toNat
    calc ((Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N)).card : ℝ)
        ≤ ((d.toNat + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ (2:ℝ) ^ d.toNat := h2
      _ = 2 ^ (d:ℝ) := by rw [← Real.rpow_natCast (2:ℝ) d.toNat, hdcast]
  · have hdneg : (d:ℝ) < 0 := by
      have hdlt : d < 0 := lt_of_not_ge hd0
      exact_mod_cast hdlt
    have hempty : Finset.filter (fun j => down_scale θ z ≤ B / 2 ^ j) (Finset.range N) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _ hj
      have hle : (j:ℝ) ≤ (d:ℝ) := (hmem j).mp hj
      have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _

open Classical in
/-- Accumulating prefix edge lengths across dyadic scales bounded by B (Lemma 7). -/
theorem accumulating_prefix_scales {α : Type*} (E : Finset α) (w : α → ℝ)
    (hw : ∀ e ∈ E, 0 < w e) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < 1)
    (B : ℝ) (hB : B ∈ shifted_dyadic_scales θ) (hB_pos : 0 < B) (N : ℕ) :
    ∑ j ∈ Finset.range N, prefix_scale_weight E w θ (B / (2 : ℝ) ^ j) ≤
      harmonic_scale_weight E w θ * B := by
  obtain ⟨m, hm⟩ := hB
  have key : ∀ e ∈ E, ∑ j ∈ Finset.range N,
      (if down_scale θ (w e) ≤ B / (2 : ℝ) ^ j then w e else 0)
        ≤ w e * (B / down_scale θ (w e)) := by
    intro e he
    have hz : 0 < w e := hw e he
    set S := Finset.filter (fun j => down_scale θ (w e) ≤ B / 2 ^ j) (Finset.range N) with hS
    have hcard : (S.card : ℝ) ≤ B / down_scale θ (w e) :=
      accumulating_prefix_scales_card_filter_le hm hz N
    have hsum : ∑ j ∈ Finset.range N,
        (if down_scale θ (w e) ≤ B / (2 : ℝ) ^ j then w e else 0) = (S.card : ℝ) * w e := by
      rw [← Finset.sum_filter, ← hS, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hcard (le_of_lt hz)]
  have hstart : ∑ j ∈ Finset.range N, prefix_scale_weight E w θ (B / (2 : ℝ) ^ j)
      = ∑ j ∈ Finset.range N, ∑ e ∈ E,
          (if down_scale θ (w e) ≤ B / (2 : ℝ) ^ j then w e else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [prefix_scale_weight, Finset.sum_filter]
  rw [hstart, Finset.sum_comm]
  calc ∑ e ∈ E, ∑ j ∈ Finset.range N,
        (if down_scale θ (w e) ≤ B / (2 : ℝ) ^ j then w e else 0)
      ≤ ∑ e ∈ E, w e * (B / down_scale θ (w e)) := Finset.sum_le_sum key
    _ = harmonic_scale_weight E w θ * B := by
        rw [harmonic_scale_weight, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        ring
