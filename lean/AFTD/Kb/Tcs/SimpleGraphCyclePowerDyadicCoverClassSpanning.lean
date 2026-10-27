import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicLayerWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverTightLongEdges
import AFTD.Kb.Tcs.CyclePowerDyadicIntWeightLeCard
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassSpanning
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# simple_graph_cycle_power_dyadic_cover_class_spanning

Topic: combinatorics   Node: 8f1c10d98775

Provenance: helper lemma. Uniform class-model bridge for OP-205 / RT-1 following arXiv:2610.15635. Transfers the proved Boolean tight-class spanning certificate to actual cycle-power cover classes; no research advance is claimed.

Every label class of an optimal m+1-layer cover at dyadic bandwidth is spanned by an endpoint-distance pair: each vertex lies in a class beginning at some offset at most 2^m-1 behind it and containing the corresponding far endpoint.
-/

set_option maxHeartbeats 3000000

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_offset_weight_eq
    (m : ℕ) (_hm : 1 ≤ m) (T : Finset ℕ) (hT : ∀ a ∈ T, a < 2 ^ m) :
    (∑ a ∈ T, (2 * (if a + 2 ^ m - 1 ∈ T then 1 else 0) +
        ∑ j ∈ Finset.range m, if j = 0 then 0 else
          if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0))
      = cycle_power_dyadic_class_weight m (fun a => decide (a ∈ T)) := by
  classical
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hA : (∑ a ∈ T, if a + 2 ^ m - 1 ∈ T then 1 else 0)
      = if (0 ∈ T ∧ 2 ^ m - 1 ∈ T) then 1 else 0 := by
    by_cases h : 0 ∈ T ∧ 2 ^ m - 1 ∈ T
    · rw [if_pos h]
      rw [Finset.sum_eq_single (0 : ℕ)]
      · simp [h.2]
      · intro b hb hb0
        have hb_lt := hT b hb
        have hnot : ¬ (b + 2 ^ m - 1 ∈ T) := by
          intro hc
          have hc_lt := hT _ hc
          omega
        simp [hnot]
      · intro h0; exact absurd h.1 h0
    · rw [if_neg h]
      refine Finset.sum_eq_zero ?_
      intro a ha
      have hnot : ¬ (a + 2 ^ m - 1 ∈ T) := by
        intro hc
        have ha_lt := hT a ha
        have hc_lt := hT _ hc
        have ha0 : a = 0 := by omega
        subst ha0
        exact h ⟨ha, by simpa using hc⟩
      simp [hnot]
  have hB : ∀ j, 1 ≤ j → j < m →
      (∑ a ∈ T, if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0)
        = ∑ i ∈ Finset.range (2 ^ j),
            (decide (i ∈ T) && decide (i + 2 ^ m - 2 ^ j ∈ T)).toNat := by
    intro j hj1 hjm
    have hjlt : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hjm
    have hbterm : ∀ i : ℕ, (decide (i ∈ T) && decide (i + 2 ^ m - 2 ^ j ∈ T)).toNat
        = if (i ∈ T ∧ i + 2 ^ m - 2 ^ j ∈ T) then 1 else 0 := by
      intro i
      by_cases h1 : i ∈ T <;> by_cases h2 : i + 2 ^ m - 2 ^ j ∈ T <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun i _ => hbterm i)]
    rw [← Finset.card_filter, ← Finset.card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨haT, hadT⟩
      exact ⟨by have := hT a haT; have := hT _ hadT; omega, haT, hadT⟩
    · rintro ⟨_, haT, hadT⟩
      exact ⟨haT, hadT⟩
  rw [cycle_power_dyadic_class_weight]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [hA]
  have hsumj : (∑ j ∈ Finset.range m, ∑ a ∈ T, if j = 0 then 0 else
          if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0)
      = ∑ j ∈ Finset.range m, if j = 0 then 0 else
          ∑ i ∈ Finset.range (2 ^ j), (decide (i ∈ T) && decide (i + 2 ^ m - 2 ^ j ∈ T)).toNat := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjm : j < m := Finset.mem_range.mp hj
      rw [if_neg hj0]
      have hinner : (∑ a ∈ T, if j = 0 then 0 else
          if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0)
          = ∑ a ∈ T, if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [if_neg hj0]
      rw [hinner]
      exact hB j hj1 hjm
  rw [hsumj]
  have hb : (decide (0 ∈ T) && decide (2 ^ m - 1 ∈ T)).toNat
      = if (0 ∈ T ∧ 2 ^ m - 1 ∈ T) then 1 else 0 := by
    by_cases h1 : 0 ∈ T <;> by_cases h2 : 2 ^ m - 1 ∈ T <;> simp [h1, h2]
  rw [hb]

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_bridge
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m) (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n) (l : ZMod n) (F : Finset (ZMod n))
    (hF : ∀ i, i ∈ F ↔ c i = l)
    (p : ZMod n) (_hpF : p ∈ F)
    (harc : ∀ u ∈ F, ∃ a : ℕ, a ≤ 2 ^ m - 1 ∧ u = p + (a : ZMod n))
    (T : Finset ℕ) (hT : ∀ a, a ∈ T ↔ a < 2 ^ m ∧ p + (a : ZMod n) ∈ F) :
    (∀ a ∈ T, a < 2 ^ m) ∧ F.card = T.card ∧
    (∑ i ∈ F, (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      = cycle_power_dyadic_class_weight m (fun a => decide (a ∈ T)) := by
  classical
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpow : 2 ^ (m+1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
  have hn2 : 2 ^ (m+1) ≤ n := by omega
  have hmn : 2 ^ m ≤ n := by omega
  have hTlt : ∀ a ∈ T, a < 2 ^ m := fun a ha => ((hT a).mp ha).1
  have hφinj : Set.InjOn (fun a : ℕ => p + (a : ZMod n)) ↑T := by
    intro a ha b hb hab
    have ha_lt : a < n := by have := hTlt a ha; omega
    have hb_lt : b < n := by have := hTlt b hb; omega
    have hcast : ((a : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := add_left_cancel hab
    exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff a b n).mp hcast) ha_lt hb_lt
  have hF_eq : F = T.image (fun a : ℕ => p + (a : ZMod n)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨a, ha, heq⟩ := harc u hu
      have haT : a ∈ T := (hT a).mpr ⟨by omega, by simpa [heq] using hu⟩
      exact Finset.mem_image.mpr ⟨a, haT, heq.symm⟩
    · intro hu
      obtain ⟨a, haT, heq⟩ := Finset.mem_image.mp hu
      simpa [heq] using ((hT a).mp haT).2
  have hcard : F.card = T.card := by
    rw [hF_eq, Finset.card_image_of_injOn hφinj]
  have arc_mem : ∀ k : ℕ, k < n → (p + ((k : ℕ) : ZMod n) ∈ F ↔ k ∈ T) := by
    intro k hk
    constructor
    · intro hmem
      obtain ⟨a, ha, heq⟩ := harc _ hmem
      have hcast : ((k : ℕ) : ZMod n) = ((a : ℕ) : ZMod n) := add_left_cancel heq
      have hmod : k ≡ a [MOD n] := (ZMod.natCast_eq_natCast_iff k a n).mp hcast
      have ha_lt : a < n := by omega
      have hka : k = a := Nat.ModEq.eq_of_lt_of_lt hmod hk ha_lt
      exact (hT k).mpr ⟨by omega, hmem⟩
    · intro hkT
      exact ((hT k).mp hkT).2
  have hpt : ∀ i ∈ F, (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0))
      = (2 * (if i + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ F then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n) ∈ F then 1 else 0)) := by
    intro i hi
    have hci : c i = l := (hF i).mp hi
    have key : ∀ z : ZMod n, (c i = c z) ↔ (z ∈ F) := by
      intro z
      rw [hci, hF z]
      exact eq_comm
    congr 1
    · by_cases h : i + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ F
      · rw [if_pos h, if_pos ((key _).mpr h)]
      · rw [if_neg h, if_neg (fun hc => h ((key _).mp hc))]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hj0 : j = 0
      · rw [if_pos hj0, if_pos hj0]
      · rw [if_neg hj0, if_neg hj0]
        by_cases h : i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n) ∈ F
        · rw [if_pos h, if_pos ((key _).mpr h)]
        · rw [if_neg h, if_neg (fun hc => h ((key _).mp hc))]
  refine ⟨hTlt, hcard, ?_⟩
  calc (∑ i ∈ F, (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      = (∑ i ∈ F, (2 * (if i + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ F then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n) ∈ F then 1 else 0))) :=
        Finset.sum_congr rfl hpt
    _ = (∑ a ∈ T, (2 * (if a + 2 ^ m - 1 ∈ T then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0))) := by
      rw [hF_eq, Finset.sum_image hφinj, ← hF_eq]
      apply Finset.sum_congr rfl
      intro a ha
      have ha_lt : a < 2 ^ m := hTlt a ha
      have hjle : ∀ j ∈ Finset.range m, j ≤ m := fun j hj => by
        have := Finset.mem_range.mp hj; omega
      have hk1 : a + (2 ^ m - 1) < n := by
        have hd : 2 ^ m - 1 < 2 ^ m := by omega
        have := Nat.add_lt_add_of_lt_of_le ha_lt (Nat.le_of_lt hd)
        omega
      have hconv1 : a + 2 ^ m - 1 = a + (2 ^ m - 1) := by
        rw [Nat.add_sub_assoc (by omega : 1 ≤ 2 ^ m) a]
      have e1 : p + (a : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n) = p + ((a + (2 ^ m - 1) : ℕ) : ZMod n) := by
        push_cast; ring
      have h1 : (p + (a : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ F) ↔ (a + (2 ^ m - 1) ∈ T) := by
        rw [e1]; exact arc_mem (a + (2 ^ m - 1)) hk1
      have hsum : ∀ j ∈ Finset.range m,
          (if j = 0 then 0 else (if p + (a : ZMod n) + ((2 ^ m - 2 ^ j : ℕ) : ZMod n) ∈ F then 1 else 0))
          = (if j = 0 then 0 else (if a + 2 ^ m - 2 ^ j ∈ T then 1 else 0)) := by
        intro j hj
        by_cases hj0 : j = 0
        · rw [if_pos hj0, if_pos hj0]
        · rw [if_neg hj0, if_neg hj0]
          have hjd : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (hjle j hj)
          have hk2 : a + (2 ^ m - 2 ^ j) < n := by
            have hd : 2 ^ m - 2 ^ j ≤ 2 ^ m := Nat.sub_le _ _
            have := Nat.add_lt_add_of_lt_of_le ha_lt hd
            omega
          have hconv2 : a + 2 ^ m - 2 ^ j = a + (2 ^ m - 2 ^ j) := by
            rw [Nat.add_sub_assoc hjd a]
          have e2 : p + (a : ZMod n) + ((2 ^ m - 2 ^ j : ℕ) : ZMod n) = p + ((a + (2 ^ m - 2 ^ j) : ℕ) : ZMod n) := by
            push_cast; ring
          rw [e2, hconv2]
          have ham := arc_mem (a + (2 ^ m - 2 ^ j)) hk2
          by_cases hh : a + (2 ^ m - 2 ^ j) ∈ T
          · rw [if_pos (ham.mpr hh), if_pos hh]
          · rw [if_neg (fun hc => hh (ham.mp hc)), if_neg hh]
      rw [hconv1]
      rw [if_congr h1 rfl rfl]
      congr 1
      exact Finset.sum_congr rfl hsum
    _ = cycle_power_dyadic_class_weight m (fun a => decide (a ∈ T)) :=
      simple_graph_cycle_power_dyadic_cover_class_spanning_offset_weight_eq m hm T hTlt

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_bool_sum_card
    (m : ℕ) (T : Finset ℕ) (hT : ∀ a ∈ T, a < 2 ^ m) :
    (∑ i ∈ Finset.range (2 ^ m), (decide (i ∈ T)).toNat) = T.card := by
  classical
  have hb : ∀ i, (decide (i ∈ T)).toNat = if i ∈ T then 1 else 0 := by
    intro i; by_cases h : i ∈ T <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hb i)]
  rw [← Finset.card_filter (fun i : ℕ => i ∈ T) (Finset.range (2 ^ m))]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hT i h, h⟩⟩

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_wt_le_card
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (l : ZMod n) :
    (∑ i ∈ Finset.univ.filter (fun i => c i = l),
      (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
    ≤ (Finset.univ.filter (fun i => c i = l)).card := by
  classical
  by_cases hne : (Finset.univ.filter (fun i => c i = l)).Nonempty
  · have hclique : ∀ u ∈ Finset.univ.filter (fun i => c i = l),
        ∀ v ∈ Finset.univ.filter (fun i => c i = l), u ≠ v →
          (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v := by
      intro u hu v hv huv
      have hu' : c u = l := (Finset.mem_filter.mp hu).2
      have hv' : c v = l := (Finset.mem_filter.mp hv).2
      exact hc u v huv (hu'.trans hv'.symm)
    obtain ⟨p, hpF, harc⟩ :=
      simple_graph_cycle_power_clique_arc n (2 ^ m - 1) hn
        (Finset.univ.filter (fun i => c i = l)) hne hclique
    set F : Finset (ZMod n) := Finset.univ.filter (fun i => c i = l) with hFdef
    set T : Finset ℕ := (Finset.range (2 ^ m)).filter (fun a : ℕ => p + (a : ZMod n) ∈ F) with hTdef
    have hF : ∀ i, i ∈ F ↔ c i = l := by
      intro i; rw [hFdef]; simp
    have hTmem : ∀ a, a ∈ T ↔ a < 2 ^ m ∧ p + (a : ZMod n) ∈ F := by
      intro a; rw [hTdef]; simp
    obtain ⟨hTlt, hcard, hcw⟩ :=
      simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_bridge m n hm hn c l F hF p hpF harc T hTmem
    rw [hcw]
    calc cycle_power_dyadic_class_weight m (fun a => decide (a ∈ T))
        ≤ (Finset.range (2 ^ m)).sum (fun i => ((fun a => decide (a ∈ T)) i).toNat) :=
          cycle_power_dyadic_class_weight_le m hm _
      _ = T.card := simple_graph_cycle_power_dyadic_cover_class_spanning_bool_sum_card m T hTlt
      _ = F.card := hcard.symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_endpoints
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (l : ZMod n) (hne : (Finset.univ.filter (fun i => c i = l)).Nonempty)
    (hwt : (∑ i ∈ Finset.univ.filter (fun i => c i = l),
      (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      = (Finset.univ.filter (fun i => c i = l)).card) :
    ∃ p : ZMod n, p ∈ (Finset.univ.filter (fun i => c i = l)) ∧
      p + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ (Finset.univ.filter (fun i => c i = l)) ∧
      (∀ u ∈ (Finset.univ.filter (fun i => c i = l)),
        ∃ a : ℕ, a ≤ 2 ^ m - 1 ∧ u = p + (a : ZMod n)) := by
  classical
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hclique : ∀ u ∈ Finset.univ.filter (fun i => c i = l),
      ∀ v ∈ Finset.univ.filter (fun i => c i = l), u ≠ v →
        (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v := by
    intro u hu v hv huv
    have hu' : c u = l := (Finset.mem_filter.mp hu).2
    have hv' : c v = l := (Finset.mem_filter.mp hv).2
    exact hc u v huv (hu'.trans hv'.symm)
  obtain ⟨p, hpF, harc⟩ :=
    simple_graph_cycle_power_clique_arc n (2 ^ m - 1) hn
      (Finset.univ.filter (fun i => c i = l)) hne hclique
  set F : Finset (ZMod n) := Finset.univ.filter (fun i => c i = l) with hFdef
  set T : Finset ℕ := (Finset.range (2 ^ m)).filter (fun a : ℕ => p + (a : ZMod n) ∈ F) with hTdef
  have hF : ∀ i, i ∈ F ↔ c i = l := by
    intro i; rw [hFdef]; simp
  have hTmem : ∀ a, a ∈ T ↔ a < 2 ^ m ∧ p + (a : ZMod n) ∈ F := by
    intro a; rw [hTdef]; simp
  obtain ⟨hTlt, hcard, hcw⟩ :=
    simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_bridge m n hm hn c l F hF p hpF harc T hTmem
  have hsumcard : (∑ i ∈ Finset.range (2 ^ m), (decide (i ∈ T)).toNat) = T.card :=
    simple_graph_cycle_power_dyadic_cover_class_spanning_bool_sum_card m T hTlt
  have hcw' : cycle_power_dyadic_class_weight m (fun a => decide (a ∈ T)) =
      (Finset.range (2 ^ m)).sum (fun i => ((fun a => decide (a ∈ T)) i).toNat) := by
    rw [← hcw, hwt, hcard, ← hsumcard]
  have hne_b : ∃ i < 2 ^ m, (fun a => decide (a ∈ T)) i = true := by
    refine ⟨0, by omega, ?_⟩
    have h0T : 0 ∈ T := (hTmem 0).mpr ⟨by omega, by simpa using hpF⟩
    simp [h0T]
  obtain ⟨hb0, hbD⟩ :=
    cycle_power_dyadic_tight_class_spanning m hm (fun a => decide (a ∈ T)) hcw' hne_b
  have h0T : 0 ∈ T := of_decide_eq_true hb0
  have hDT : 2 ^ m - 1 ∈ T := of_decide_eq_true hbD
  have hpF' : p ∈ F := by simpa using ((hTmem 0).mp h0T).2
  have hpD' : p + ((2 ^ m - 1 : ℕ) : ZMod n) ∈ F := ((hTmem (2 ^ m - 1)).mp hDT).2
  exact ⟨p, hpF', hpD', harc⟩

private theorem simple_graph_cycle_power_dyadic_cover_class_spanning_layer_weight_eq
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v) :
    ∀ s : Fin (m+1),
      (∑ i : ZMod n, (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0))) = n := by
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
  intro s
  by_contra hne
  have hlt : W s < n := lt_of_le_of_ne (hW_le s) hne
  have hconst : ∑ _x : Fin (m+1), n = (m+1) * n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have hstrict : ∑ x : Fin (m+1), W x < ∑ _x : Fin (m+1), n :=
    Finset.sum_lt_sum (fun x _ => hW_le x) ⟨s, Finset.mem_univ s, hlt⟩
  rw [hconst, hsum_eq] at hstrict
  exact lt_irrefl _ hstrict

theorem simple_graph_cycle_power_dyadic_cover_class_spanning
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v) :
    ∀ (s : Fin (m + 1)) (v : ZMod n),
      ∃ a : ℕ, a ≤ 2 ^ m - 1 ∧
        c s (v - (a : ZMod n)) = c s v ∧
        c s (v - (a : ZMod n)) =
          c s (v - (a : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) := by
  classical
  have hlayer := simple_graph_cycle_power_dyadic_cover_class_spanning_layer_weight_eq m n hm hn c hc hcov
  intro s v
  have hsum_eq : (∑ l : ZMod n, (∑ i ∈ Finset.univ.filter (fun i => c s i = l),
      (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))) = n := by
    rw [Finset.sum_fiberwise]
    simpa using hlayer s
  have hcard_eq : (∑ l : ZMod n, (Finset.univ.filter (fun i => c s i = l)).card) = n := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := c s) (by intro x _; simp)]
    simp
  have hle : ∀ l, (∑ i ∈ Finset.univ.filter (fun i => c s i = l),
      (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      ≤ (Finset.univ.filter (fun i => c s i = l)).card := by
    intro l
    exact simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_wt_le_card m n hm hn (c s) (hc s) l
  have heq_each : ∀ l, (∑ i ∈ Finset.univ.filter (fun i => c s i = l),
      (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      = (Finset.univ.filter (fun i => c s i = l)).card := by
    intro l
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (ZMod n)))
      (f := fun l => ∑ i ∈ Finset.univ.filter (fun i => c s i = l),
        (2 * (if c s i = c s (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if c s i = c s (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      (g := fun l => (Finset.univ.filter (fun i => c s i = l)).card)
      (fun l _ => hle l)).mp (by rw [hsum_eq, hcard_eq])
    exact hall l (Finset.mem_univ l)
  have hl := heq_each (c s v)
  have hnev : (Finset.univ.filter (fun i => c s i = c s v)).Nonempty := ⟨v, by simp⟩
  obtain ⟨p, hpF, hpD, harc⟩ :=
    simple_graph_cycle_power_dyadic_cover_class_spanning_fibre_endpoints m n hm hn (c s) (hc s) (c s v) hnev hl
  have hvF : v ∈ Finset.univ.filter (fun i => c s i = c s v) := by simp
  obtain ⟨a0, ha0le, ha0eq⟩ := harc v hvF
  refine ⟨a0, ha0le, ?_, ?_⟩
  · have hvc : v - (a0 : ZMod n) = p := by rw [ha0eq, add_sub_cancel_right]
    rw [hvc]
    exact (Finset.mem_filter.mp hpF).2
  · have hvc : v - (a0 : ZMod n) = p := by rw [ha0eq, add_sub_cancel_right]
    rw [hvc]
    exact ((Finset.mem_filter.mp hpF).2).trans ((Finset.mem_filter.mp hpD).2).symm
