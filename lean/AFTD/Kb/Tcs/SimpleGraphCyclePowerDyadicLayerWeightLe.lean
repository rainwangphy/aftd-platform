import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerCliqueArc
import AFTD.Kb.Tcs.CyclePowerDyadicIntWeightLeCard
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.F

/-!
# simple_graph_cycle_power_dyadic_layer_weight_le

Topic: combinatorics   Node: 4477d8cb012e

Provenance: helper lemma. Uniform weighted-cover reduction for OP-205 / RT-1 following arXiv:2610.15635. This is the arbitrary-bandwidth analogue of the proved k=3 and k=7 layer-weight helpers; no research advance is claimed.

In any clique labelling of a cycle power with dyadic bandwidth 2^m-1 and n at least three times the bandwidth plus one, the total layer weight (two for endpoint-distance pairs, one for other dyadic long distances) is at most n.
-/

private theorem simple_graph_cycle_power_dyadic_layer_weight_le_fiber
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
  set F := Finset.univ.filter (fun i : ZMod n => c i = l) with hFdef
  set W : ZMod n → ℕ := fun i =>
    2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
      (Finset.range m).sum (fun j => if j = 0 then 0 else
        if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) with hWdef
  change (∑ i ∈ F, W i) ≤ F.card
  by_cases hne : F.Nonempty
  · obtain ⟨p, hpF, harc⟩ := simple_graph_cycle_power_clique_arc n (2 ^ m - 1) hn F hne (by
      intro u hu v hv huv
      rw [hFdef] at hu hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact hc u v huv (by rw [hu, hv]))
    set T : Finset ℕ := (Finset.range (2 ^ m)).filter (fun a => p + (a : ZMod n) ∈ F) with hTdef
    set T' : Finset ℤ := T.image (fun a : ℕ => (a : ℤ)) with hT'def
    have h1 : 1 ≤ 2 ^ m := by have := Nat.one_lt_two_pow (by omega : m ≠ 0); omega
    have hKlt : 2 ^ m - 1 < n := by omega
    have h2Klt : 2 * (2 ^ m - 1) < n := by omega
    have hsub : ((2 ^ m - 1 : ℕ) : ℤ) = (2 ^ m : ℤ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    have hmemF : ∀ u : ZMod n, u ∈ F ↔ c u = l := by
      intro u; rw [hFdef]; simp
    have hpF' : c p = l := (hmemF p).mp hpF
    have hW' : ∀ i : ZMod n, W i =
        2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0) := by
      intro i; rw [hWdef]
    have hT_mem : ∀ a, a ∈ T ↔ a < 2 ^ m ∧ p + (a : ZMod n) ∈ F := by
      intro a; rw [hTdef]; simp [Finset.mem_range]
    have hT'_mem : ∀ e : ℕ, ((e : ℤ) ∈ T') ↔ e ∈ T := by
      intro e
      rw [hT'def, Finset.mem_image]
      constructor
      · rintro ⟨b, hb, hbe⟩
        have hbe' : b = e := Int.ofNat_inj.mp hbe
        rwa [hbe'] at hb
      · intro he; exact ⟨e, he, rfl⟩
    have hinj : Set.InjOn (fun a : ℕ => p + (a : ZMod n)) ↑T := by
      intro a ha b hb hab
      have ha_lt : a < 2 ^ m := ((hT_mem a).mp ha).1
      have hb_lt : b < 2 ^ m := ((hT_mem b).mp hb).1
      have hcast : (a : ZMod n) = (b : ZMod n) := add_left_cancel hab
      have han : a < n := by omega
      have hbn : b < n := by omega
      rw [ZMod.natCast_eq_natCast_iff] at hcast
      exact Nat.ModEq.eq_of_lt_of_lt hcast han hbn
    have hF_eq : F = T.image (fun a : ℕ => p + (a : ZMod n)) := by
      ext u
      rw [Finset.mem_image]
      constructor
      · intro hu
        obtain ⟨a, ha_le, ha_eq⟩ := harc u hu
        refine ⟨a, ?_, ha_eq.symm⟩
        rw [hT_mem]
        exact ⟨by omega, by rw [← ha_eq]; exact hu⟩
      · rintro ⟨a, ha, rfl⟩
        exact ((hT_mem a).mp ha).2
    have hcard1 : F.card = T.card := by
      rw [hF_eq, Finset.card_image_of_injOn hinj]
    have hcard2 : T'.card = T.card := by
      rw [hT'def, Finset.card_image_of_injOn (by intro x _ y _ h; exact Int.ofNat_inj.mp h)]
    have hsum1 : ∑ i ∈ F, W i = ∑ a ∈ T, W (p + (a : ZMod n)) := by
      rw [hF_eq, Finset.sum_image hinj]
    have hshift : ∀ a d : ℕ, a < 2 ^ m → d < 2 ^ m →
        (p + ((a + d : ℕ) : ZMod n) ∈ F ↔ (a + d) ∈ T) := by
      intro a d ha hd
      constructor
      · intro hmem
        obtain ⟨b, hb_le, hb_eq⟩ := harc _ hmem
        have hcast : ((a + d : ℕ) : ZMod n) = (b : ZMod n) := add_left_cancel hb_eq
        have hadn : a + d < n := by omega
        have hbn : b < n := by omega
        rw [ZMod.natCast_eq_natCast_iff] at hcast
        have hab : a + d = b := Nat.ModEq.eq_of_lt_of_lt hcast hadn hbn
        rw [hT_mem]
        exact ⟨by omega, hmem⟩
      · intro hmem
        exact ((hT_mem (a + d)).mp hmem).2
    have hif : ∀ d : ℕ, d < 2 ^ m → ∀ a ∈ T,
        (if c (p + (a : ZMod n)) = c (p + (a : ZMod n) + (d : ZMod n)) then (1:ℕ) else 0)
        = (if (a : ℤ) + (d : ℤ) ∈ T' then 1 else 0) := by
      intro d hd a ha
      have ha_lt : a < 2 ^ m := ((hT_mem a).mp ha).1
      have haF : p + (a : ZMod n) ∈ F := ((hT_mem a).mp ha).2
      have hca : c (p + (a : ZMod n)) = l := (hmemF _).mp haF
      have hstep : p + (a : ZMod n) + (d : ZMod n) = p + ((a + d : ℕ) : ZMod n) := by
        push_cast; ring
      have hiff : c (p + (a : ZMod n)) = c (p + (a : ZMod n) + (d : ZMod n)) ↔
          ((a : ℤ) + (d : ℤ) ∈ T') := by
        rw [hstep, hca]
        have e1 : l = c (p + ((a + d : ℕ) : ZMod n)) ↔ p + ((a + d : ℕ) : ZMod n) ∈ F := by
          rw [hmemF]; exact eq_comm
        have e2 : p + ((a + d : ℕ) : ZMod n) ∈ F ↔ (a + d) ∈ T := hshift a d ha_lt hd
        have e3 : (a + d) ∈ T ↔ ((a + d : ℕ) : ℤ) ∈ T' := (hT'_mem (a + d)).symm
        have e4 : ((a + d : ℕ) : ℤ) ∈ T' ↔ ((a : ℤ) + (d : ℤ)) ∈ T' := by rw [Nat.cast_add]
        exact e1.trans (e2.trans (e3.trans e4))
      exact if_congr hiff rfl rfl
    have hterm : ∀ a ∈ T, W (p + (a : ZMod n)) =
        2 * (if ((a : ℤ) + ((2 ^ m - 1 : ℕ) : ℤ)) ∈ T' then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if ((a : ℤ) + ((2 ^ m - 2 ^ j : ℕ) : ℤ)) ∈ T' then 1 else 0) := by
      intro a ha
      rw [hW', hif (2 ^ m - 1) (by have := Nat.two_pow_pos m; omega) a ha]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · rw [if_neg hj0, if_neg hj0]
        exact hif (2 ^ m - 2 ^ j) (by have := Nat.two_pow_pos m; have := Nat.two_pow_pos j; omega) a ha
    have hinjT' : Set.InjOn (fun a : ℕ => (a : ℤ)) ↑T := by
      intro x _ y _ h; exact Int.ofNat_inj.mp h
    have hsum2 : ∑ a ∈ T, W (p + (a : ZMod n)) =
        ∑ e ∈ T', (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ T' then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ T' then 1 else 0)) := by
      rw [Finset.sum_congr rfl hterm,
        ← Finset.sum_image (f := fun e => 2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ T' then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ T' then 1 else 0)) hinjT',
        ← hT'def]
    have hdiam : ∀ a ∈ T', ∀ b ∈ T', |a - b| ≤ ((2 ^ m - 1 : ℕ) : ℤ) := by
      intro a ha b hb
      rw [hT'def, Finset.mem_image] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have ha'_lt : a' < 2 ^ m := ((hT_mem a').mp ha').1
      have hb'_lt : b' < 2 ^ m := ((hT_mem b').mp hb').1
      have ha'_le : (a' : ℤ) ≤ (2 ^ m : ℤ) - 1 := by
        have : (a' : ℤ) < (2 ^ m : ℤ) := by exact_mod_cast ha'_lt
        omega
      have hb'_le : (b' : ℤ) ≤ (2 ^ m : ℤ) - 1 := by
        have : (b' : ℤ) < (2 ^ m : ℤ) := by exact_mod_cast hb'_lt
        omega
      rw [abs_le, hsub]
      constructor <;> omega
    have hbound := cycle_power_dyadic_int_weight_le_card m hm T' hdiam
    rw [hsum1, hsum2]
    calc (∑ e ∈ T', (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ T' then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ T' then 1 else 0)))
        ≤ T'.card := hbound
      _ = F.card := by rw [hcard2, ← hcard1]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

theorem simple_graph_cycle_power_dyadic_layer_weight_le
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v) :
    (∑ i : ZMod n,
      (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0))) ≤ n := by
  classical
  calc (∑ i : ZMod n,
        (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
          (Finset.range m).sum (fun j => if j = 0 then 0 else
            if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)))
      = ∑ l : ZMod n, ∑ i ∈ Finset.univ.filter (fun i => c i = l),
          (2 * (if c i = c (i + ((2 ^ m - 1 : ℕ) : ZMod n)) then 1 else 0) +
            (Finset.range m).sum (fun j => if j = 0 then 0 else
              if c i = c (i + ((2 ^ m - 2 ^ j : ℕ) : ZMod n)) then 1 else 0)) := by
        rw [Finset.sum_fiberwise]
    _ ≤ ∑ l : ZMod n, (Finset.univ.filter (fun i => c i = l)).card :=
        Finset.sum_le_sum (fun l _ =>
          simple_graph_cycle_power_dyadic_layer_weight_le_fiber m n hm hn c hc l)
    _ = n := by
        rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
              (f := c) (by intro x _; simp)]
        simp [ZMod.card]
