import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenLayerWeightLe
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenCoverFourTight
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_cycle_power_seven_layer_weight_eq_class_five_imp_one_two_imp_six

Topic: combinatorics   Node: af6ab9968854

Provenance: helper lemma. helper for RT-1 (k = 7 case of OP-205, arXiv:2610.15635): the hypotheses h51, h26 of cycle_power_seven_tight_type_sequence_one_iff_six; the tight class types have weight equal to size, and weight(T) − |T| = [1,5 ∈ T] + [2,6 ∈ T] − [5 ∈ T] − [2 ∈ T] for {0,7} ⊆ T ⊆ [0,7]

Let c label the vertices of C_n^7 (n ≥ 22) so that every label class is a clique, with total weight Σ_i (2·[i ~ i+7] + [i ~ i+6] + [i ~ i+4]) exactly n. Then every class containing i and i+7 is tight: if it contains i+5 it contains i+1, and if it contains i+2 it contains i+6.
-/

open Finset in
theorem simple_graph_cycle_power_seven_layer_weight_eq_class_core (n : ℕ) [NeZero n]
    (hn : 22 ≤ n) (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 7).Adj u v)
    (heq : ∑ i : ZMod n, (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
      + (if c i = c (i + 4) then 1 else 0)) = n)
    (i : ZMod n) (h7 : c i = c (i + 7)) :
    (c i = c (i + 5) → c i = c (i + 1)) ∧ (c i = c (i + 2) → c i = c (i + 6)) := by
  have hdec : ∀ T ∈ (Icc (0 : ℤ) 7).powerset, (0 : ℤ) ∈ T → (7 : ℤ) ∈ T →
      simple_graph_cycle_power_seven_layer_weight_int_weight T = T.card →
      ((5 : ℤ) ∈ T → (1 : ℤ) ∈ T) ∧ ((2 : ℤ) ∈ T → (6 : ℤ) ∈ T) := by
    decide +kernel
  let W : ZMod n → ℕ := fun i => 2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
    + (if c i = c (i + 4) then 1 else 0)
  have h_fiber := sum_fiberwise (s := univ) c W
  have h_card : (∑ j : ZMod n, #{x | c x = j}) = n := by
    have := card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := c) (fun _ _ => mem_univ _)
    rw [← this, card_univ, ZMod.card]
  have h_le : ∀ j, ∑ x with c x = j, W x ≤ #{x | c x = j} := by
    intro j
    exact simple_graph_cycle_power_seven_layer_weight_fiber_le n hn c hc j
  have h_sum_W : (∑ j : ZMod n, ∑ x with c x = j, W x) = ∑ j : ZMod n, #{x | c x = j} := by
    rw [h_fiber, heq, h_card]
  have h_fiber_eq : ∀ ℓ, ∑ x with c x = ℓ, W x = #{x | c x = ℓ} := by
    intro ℓ
    by_contra hne
    have hlt : (∑ x with c x = ℓ, W x) < #{x | c x = ℓ} := lt_of_le_of_ne (h_le ℓ) hne
    have h_sum_lt := sum_lt_sum (s := univ) (fun j _ => h_le j) ⟨ℓ, mem_univ ℓ, hlt⟩
    omega
  let K := univ.filter (fun x => c x = c i)
  let S : Finset ℤ := (Icc (-7 : ℤ) 7).filter (fun (e : ℤ) => c (i + (e : ZMod n)) = c i)
  have hS_sub : S ⊆ Icc (-7 : ℤ) 7 := filter_subset _ _
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
        rcases (simple_graph_cycle_power_seven_adj_iff n hn i y).mp hadj with ⟨e, he0, he7, rfl⟩
        rw [abs_le] at he7
        refine ⟨e, ?_, rfl⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, hy_c⟩
  have hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 7 := by
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
      rcases (simple_graph_cycle_power_seven_adj_iff n hn (i + (a : ZMod n)) (i + (b : ZMod n))).mp hadj with ⟨d, hd0, hd7, hdeq⟩
      rw [abs_le] at hd7
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
  have h_mem : ∀ z ∈ K, ∃ e ∈ Icc (-7 : ℤ) 7, z = i + (e : ZMod n) := by
    intro z hz
    rw [mem_filter] at hz
    by_cases hzi : z = i
    · subst hzi; refine ⟨0, by simp [mem_Icc], by simp⟩
    · have hadj := hc i z (Ne.symm hzi) (hz.2.symm)
      rcases (simple_graph_cycle_power_seven_adj_iff n hn i z).mp hadj with ⟨e, he0, he7, rfl⟩
      rw [abs_le] at he7
      refine ⟨e, by rw [mem_Icc]; constructor <;> omega, rfl⟩
  have h_shift : ∀ e ∈ S, ∀ (k : ℤ), k = 4 ∨ k = 6 ∨ k = 7 →
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
        rcases hk with rfl | rfl | rfl <;> constructor <;> omega
      have h_eq : e + k = e' := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (e + k) e' hdiff).mp he_eq'
      subst h_eq
      exact ⟨he', hc_shift⟩
    · intro h
      exact h.2
  have h_sum : ∑ x ∈ K, W x = simple_graph_cycle_power_seven_layer_weight_int_weight S := by
    unfold simple_graph_cycle_power_seven_layer_weight_int_weight
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
        rcases (simple_graph_cycle_power_seven_adj_iff n hn i y).mp hadj with ⟨e, he0, he7, rfl⟩
        rw [abs_le] at he7
        refine ⟨e, ?_, rfl⟩
        rw [mem_filter, mem_Icc]; refine ⟨⟨by omega, by omega⟩, hy_c⟩
    · intro e he
      have he_c : c (i + (e : ZMod n)) = c i := (mem_filter.mp he).2
      have h7 := h_shift e he 7 (Or.inr (Or.inr rfl))
      have h6 := h_shift e he 6 (Or.inr (Or.inl rfl))
      have h4 := h_shift e he 4 (Or.inl rfl)
      have h7_eq : (c (i + (e : ZMod n)) = c (i + (e : ZMod n) + 7)) ↔ (e + 7 ∈ S) := by
        rw [he_c]
        have : (7 : ZMod n) = ((7 : ℤ) : ZMod n) := by push_cast; rfl
        rw [this, eq_comm]
        exact h7
      have h6_eq : (c (i + (e : ZMod n)) = c (i + (e : ZMod n) + 6)) ↔ (e + 6 ∈ S) := by
        rw [he_c]
        have : (6 : ZMod n) = ((6 : ℤ) : ZMod n) := by push_cast; rfl
        rw [this, eq_comm]
        exact h6
      have h4_eq : (c (i + (e : ZMod n)) = c (i + (e : ZMod n) + 4)) ↔ (e + 4 ∈ S) := by
        rw [he_c]
        have : (4 : ZMod n) = ((4 : ℤ) : ZMod n) := by push_cast; rfl
        rw [this, eq_comm]
        exact h4
      dsimp [W]
      rw [if_congr h7_eq rfl rfl, if_congr h6_eq rfl rfl, if_congr h4_eq rfl rfl]
  have h_weight_eq : simple_graph_cycle_power_seven_layer_weight_int_weight S = #S := by
    rw [← h_sum, h_card_eq]
    exact h_fiber_eq (c i)
  have h0S : (0 : ℤ) ∈ S := by
    rw [mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by simp⟩
  have h7S : (7 : ℤ) ∈ S := by
    rw [mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    push_cast; exact h7.symm
  have hsubS : S ⊆ Icc 0 7 := by
    intro e he
    have h1 := hdiam e he 0 h0S
    have h2 := hdiam e he 7 h7S
    rw [abs_le] at h1 h2
    rw [mem_Icc]; constructor <;> omega
  have hT := hdec S (mem_powerset.mpr hsubS) h0S h7S h_weight_eq
  have hmem : ∀ k : ℤ, 0 ≤ k → k ≤ 7 → (k ∈ S ↔ c i = c (i + (k : ZMod n))) := by
    intro k hk0 hk7
    rw [mem_filter, mem_Icc]
    constructor
    · rintro ⟨-, h⟩; exact h.symm
    · intro h; exact ⟨⟨by omega, by omega⟩, h.symm⟩
  constructor
  · intro h5
    have := (hmem 1 (by norm_num) (by norm_num)).mp
      (hT.1 ((hmem 5 (by norm_num) (by norm_num)).mpr (by push_cast; exact h5)))
    push_cast at this; exact this
  · intro h2
    have := (hmem 6 (by norm_num) (by norm_num)).mp
      (hT.2 ((hmem 2 (by norm_num) (by norm_num)).mpr (by push_cast; exact h2)))
    push_cast at this; exact this

theorem simple_graph_cycle_power_seven_layer_weight_eq_class_five_imp_one_two_imp_six (n : ℕ) [NeZero n]
    (hn : 22 ≤ n) (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 7).Adj u v)
    (heq : ∑ i : ZMod n, (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
      + (if c i = c (i + 4) then 1 else 0)) = n)
    (i : ZMod n) (h7 : c i = c (i + 7)) :
    (c i = c (i + 5) → c i = c (i + 1)) ∧ (c i = c (i + 2) → c i = c (i + 6)) :=
  simple_graph_cycle_power_seven_layer_weight_eq_class_core n hn c hc heq i h7
