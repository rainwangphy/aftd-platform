import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeLayerWeightLe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeAdjIff
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt

/-!
# simple_graph_cycle_power_three_layer_weight_eq_imp

Topic: combinatorics   Node: 850ae8a7a87f

Provenance: helper lemma. Step toward simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd (the k = 3 case of OP-205, arXiv:2610.15635): the double-counting proof found in thread RT-1.

In the situation of the weight inequality, if Σ_i (2·[c i = c(i+3)] + [c i = c(i+2)]) = n then every class contains a pair at distance 3 with all its elements between them: every vertex i lies in the class of some j ∈ {i-3, ..., i} with c j = c (j+3).
-/

open Finset

theorem simple_graph_cycle_power_three_layer_weight_decide_diam_tight (S : Finset ℤ)
    (hS : S ⊆ Icc (-3 : ℤ) 3)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 3)
    (heq : simple_graph_cycle_power_three_layer_weight_int_weight S = #S)
    (hne : S.Nonempty) :
    ∃ a ∈ S, a + 3 ∈ S ∧ ∀ x ∈ S, a ≤ x ∧ x ≤ a + 3 := by
  have h_univ : S ∈ (Icc (-3 : ℤ) 3).powerset := mem_powerset.mpr hS
  revert S hS hdiam heq hne h_univ
  decide

theorem simple_graph_cycle_power_three_layer_weight_eq_imp (n : ℕ) [NeZero n] (hn : 10 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 3).Adj u v)
    (heq : ∑ i : ZMod n,
      (2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0)) = n) :
    ∀ i : ZMod n, ∃ d : ℕ, d ≤ 3 ∧ c (i - d) = c (i - d + 3) ∧ c (i - d) = c i := by
  intro i
  let W : ZMod n → ℕ := fun i => 2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0)
  have h_fiber := sum_fiberwise (s := univ) c W
  have h_card : (∑ j : ZMod n, #{x | c x = j}) = n := by
    have := card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := c) (fun _ _ => mem_univ _)
    rw [← this, card_univ, ZMod.card]
  have h_le : ∀ j, ∑ x with c x = j, W x ≤ #{x | c x = j} := by
    intro j
    exact simple_graph_cycle_power_three_layer_weight_fiber_le n hn c hc j
  have h_sum_W : (∑ j : ZMod n, ∑ x with c x = j, W x) = ∑ j : ZMod n, #{x | c x = j} := by
    rw [h_fiber, heq, h_card]
  have h_fiber_eq : ∀ ℓ, ∑ x with c x = ℓ, W x = #{x | c x = ℓ} := by
    intro ℓ
    by_contra hne
    have hlt : (∑ x with c x = ℓ, W x) < #{x | c x = ℓ} := lt_of_le_of_ne (h_le ℓ) hne
    have h_sum_lt := sum_lt_sum (s := univ) (fun j _ => h_le j) ⟨ℓ, mem_univ ℓ, hlt⟩
    omega
  let K := univ.filter (fun x => c x = c i)
  let S : Finset ℤ := (Icc (-3 : ℤ) 3).filter (fun (e : ℤ) => c (i + (e : ZMod n)) = c i)
  have hS_sub : S ⊆ Icc (-3 : ℤ) 3 := filter_subset _ _
  have h_card_eq : #S = #K := by
    apply Finset.card_bij (s := S) (t := K) (fun e _ => i + (e : ZMod n))
    · intro e he
      rw [mem_filter]
      exact ⟨mem_univ _, (mem_filter.mp he).2⟩
    · intro a ha b hb hab
      have ha_icc := (mem_filter.mp ha).1
      have hb_icc := (mem_filter.mp hb).1
      rw [mem_Icc] at ha_icc hb_icc
      have hab_eq : (a : ZMod n) = (b : ZMod n) := add_left_cancel hab
      have h_diff : |a - b| < n := by
        rw [abs_lt]; constructor <;> omega
      exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b h_diff).mp hab_eq
    · intro y hy
      have hy_c : c y = c i := (mem_filter.mp hy).2
      by_cases hyi : y = i
      · subst hyi; refine ⟨0, ?_, by simp⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, by simp⟩
      · have hadj := hc i y (Ne.symm hyi) (hy_c.symm)
        rcases (simple_graph_cycle_power_three_adj_iff n hn i y).mp hadj with ⟨e, he0, he3, rfl⟩
        rw [abs_le] at he3
        refine ⟨e, ?_, rfl⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, hy_c⟩
  have hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 3 := by
    intro a ha b hb
    have ha_icc := (mem_filter.mp ha).1
    have hb_icc := (mem_filter.mp hb).1
    have ha_c := (mem_filter.mp ha).2
    have hb_c := (mem_filter.mp hb).2
    rw [mem_Icc] at ha_icc hb_icc
    by_cases hab : a = b
    · subst hab; simp
    · have hne : (i + (a : ZMod n)) ≠ (i + (b : ZMod n)) := by
        intro heq'
        have hab_eq : (a : ZMod n) = (b : ZMod n) := add_left_cancel heq'
        have h_diff : |a - b| < n := by
          rw [abs_lt]; constructor <;> omega
        exact hab ((zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b h_diff).mp hab_eq)
      have hadj := hc (i + (a : ZMod n)) (i + (b : ZMod n)) hne (ha_c.trans hb_c.symm)
      rcases (simple_graph_cycle_power_three_adj_iff n hn (i + (a : ZMod n)) (i + (b : ZMod n))).mp hadj with ⟨d, hd0, hd3, hdeq⟩
      rw [abs_le] at hd3
      have h_diff : |b - (a + d)| < n := by
        rw [abs_lt]; constructor <;> omega
      have h_eq' : ((b : ZMod n) = ((a + d : ℤ) : ZMod n)) := by
        have : i + (b : ZMod n) = i + ((a + d : ℤ) : ZMod n) := by
          rw [hdeq]; push_cast; ring
        exact add_left_cancel this
      have h_bd := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n b (a + d) h_diff).mp h_eq'
      subst h_bd
      have : a - (a + d) = -d := by ring
      rw [this, abs_neg, abs_le]
      constructor <;> omega
  have h_mem : ∀ z ∈ K, ∃ e ∈ Icc (-3 : ℤ) 3, z = i + (e : ZMod n) := by
    intro z hz
    rw [mem_filter] at hz
    by_cases hzi : z = i
    · subst hzi; refine ⟨0, by simp [mem_Icc], by simp⟩
    · have hadj := hc i z (Ne.symm hzi) (hz.2.symm)
      rcases (simple_graph_cycle_power_three_adj_iff n hn i z).mp hadj with ⟨e, he0, he3, rfl⟩
      rw [abs_le] at he3
      refine ⟨e, by rw [mem_Icc]; constructor <;> omega, rfl⟩
  have h_shift : ∀ e ∈ S, ∀ (k : ℤ), k = 2 ∨ k = 3 →
      (c (i + (e : ZMod n) + (k : ZMod n)) = c i ↔ e + k ∈ S) := by
    intro e he k hk
    have he_icc := (mem_filter.mp he).1
    rw [mem_Icc] at he_icc
    rw [mem_filter, mem_Icc]
    have hk_cast : i + (e : ZMod n) + (k : ZMod n) = i + ((e + k : ℤ) : ZMod n) := by push_cast; ring
    rw [hk_cast]
    constructor
    · intro hc_shift
      have hz_mem : i + ((e + k : ℤ) : ZMod n) ∈ K := by
        rw [mem_filter]; exact ⟨mem_univ _, hc_shift⟩
      rcases h_mem _ hz_mem with ⟨e', he', he'_eq⟩
      have he_eq' : ((e + k : ℤ) : ZMod n) = (e' : ZMod n) := add_left_cancel he'_eq
      rw [mem_Icc] at he'
      have hdiff : |(e + k) - e'| < n := by
        rw [abs_lt]
        rcases hk with rfl | rfl <;> constructor <;> omega
      have h_eq : e + k = e' := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (e + k) e' hdiff).mp he_eq'
      subst h_eq
      exact ⟨he', hc_shift⟩
    · intro h
      exact h.2
  have h_sum : ∑ x ∈ K, W x = simple_graph_cycle_power_three_layer_weight_int_weight S := by
    unfold simple_graph_cycle_power_three_layer_weight_int_weight
    symm
    apply sum_bij (s := S) (t := K) (fun e _ => i + (e : ZMod n))
    · intro e he
      rw [mem_filter]
      exact ⟨mem_univ _, (mem_filter.mp he).2⟩
    · intro a ha b hb hab
      have ha_icc := (mem_filter.mp ha).1
      have hb_icc := (mem_filter.mp hb).1
      rw [mem_Icc] at ha_icc hb_icc
      have hab_eq : (a : ZMod n) = (b : ZMod n) := add_left_cancel hab
      have h_diff : |a - b| < n := by
        rw [abs_lt]; constructor <;> omega
      exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b h_diff).mp hab_eq
    · intro y hy
      have hy_c := (mem_filter.mp hy).2
      by_cases hyi : y = i
      · subst hyi; refine ⟨0, ?_, by simp⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, by simp⟩
      · have hadj := hc i y (Ne.symm hyi) (hy_c.symm)
        rcases (simple_graph_cycle_power_three_adj_iff n hn i y).mp hadj with ⟨e, he0, he3, rfl⟩
        rw [abs_le] at he3
        refine ⟨e, ?_, rfl⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, hy_c⟩
    · intro e he
      have he_c : c (i + (e : ZMod n)) = c i := (mem_filter.mp he).2
      have h3 := h_shift e he 3 (Or.inr rfl)
      have h2 := h_shift e he 2 (Or.inl rfl)
      have h3_eq : (c (i + (e : ZMod n)) = c (i + (e : ZMod n) + 3)) ↔ (e + 3 ∈ S) := by
        rw [he_c]
        have : (3 : ZMod n) = ((3 : ℤ) : ZMod n) := by push_cast; rfl
        rw [this, eq_comm]
        exact h3
      have h2_eq : (c (i + (e : ZMod n)) = c (i + (e : ZMod n) + 2)) ↔ (e + 2 ∈ S) := by
        rw [he_c]
        have : (2 : ZMod n) = ((2 : ℤ) : ZMod n) := by push_cast; rfl
        rw [this, eq_comm]
        exact h2
      dsimp [W]
      rw [if_congr h3_eq rfl rfl, if_congr h2_eq rfl rfl]
  have h_weight_eq : simple_graph_cycle_power_three_layer_weight_int_weight S = #S := by
    rw [← h_sum, h_card_eq]
    exact h_fiber_eq (c i)
  have h0_in_S : (0 : ℤ) ∈ S := by
    rw [mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by simp⟩
  have hne : S.Nonempty := ⟨0, h0_in_S⟩
  rcases simple_graph_cycle_power_three_layer_weight_decide_diam_tight S hS_sub hdiam h_weight_eq hne
    with ⟨a, ha, ha3, h_bounds⟩
  have ha_bounds := h_bounds 0 h0_in_S
  have ha_le_0 : a ≤ 0 := ha_bounds.1
  have h_0_le_a3 : 0 ≤ a + 3 := ha_bounds.2
  have h_d_le_3 : (-a).toNat ≤ 3 := by omega
  refine ⟨(-a).toNat, h_d_le_3, ?_, ?_⟩
  · have ha_eq : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have ha_cast : (((-a).toNat : ℕ) : ZMod n) = - (a : ZMod n) := by
      rw [← Int.cast_natCast, ha_eq, Int.cast_neg]
    have ha_mem : c (i + (a : ZMod n)) = c i := (mem_filter.mp ha).2
    have ha3_mem : c (i + ((a + 3 : ℤ) : ZMod n)) = c i := (mem_filter.mp ha3).2
    have h1 : i - (((-a).toNat : ℕ) : ZMod n) = i + (a : ZMod n) := by
      rw [ha_cast, sub_neg_eq_add]
    have h2 : i - (((-a).toNat : ℕ) : ZMod n) + 3 = i + ((a + 3 : ℤ) : ZMod n) := by
      rw [h1]; push_cast; ring
    rw [h2, h1, ha_mem, ha3_mem]
  · have ha_eq : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have ha_cast : (((-a).toNat : ℕ) : ZMod n) = - (a : ZMod n) := by
      rw [← Int.cast_natCast, ha_eq, Int.cast_neg]
    have ha_mem : c (i + (a : ZMod n)) = c i := (mem_filter.mp ha).2
    have h1 : i - (((-a).toNat : ℕ) : ZMod n) = i + (a : ZMod n) := by
      rw [ha_cast, sub_neg_eq_add]
    rw [h1, ha_mem]
