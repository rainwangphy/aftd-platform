import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SimpleGraphCyclePowerThreeAdjIff
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.G

/-!
# simple_graph_cycle_power_three_layer_weight_le

Topic: combinatorics   Node: b5d66c4dec46

Provenance: helper lemma. Step toward simple_graph_not_has_equivalence_cover_cycle_power_three_of_not_dvd (the k = 3 case of OP-205, arXiv:2610.15635): the double-counting proof found in thread RT-1.

Let n ≥ 10 and let c label the vertices of C_n^3 so that every label class is a clique. Then Σ_i (2·[i and i+3 share a class] + [i and i+2 share a class]) ≤ n: each class K contributes 2·(its pairs at distance 3) + (its pairs at distance 2) ≤ |K|.
-/

open Finset

def simple_graph_cycle_power_three_layer_weight_int_weight (T : Finset ℤ) : ℕ :=
  ∑ e ∈ T, (2 * (if e + 3 ∈ T then 1 else 0) + (if e + 2 ∈ T then 1 else 0))

theorem simple_graph_cycle_power_three_layer_weight_decide_diam (S : Finset ℤ)
    (hS : S ⊆ Icc (-3 : ℤ) 3)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 3) :
    simple_graph_cycle_power_three_layer_weight_int_weight S ≤ #S := by
  have h_univ : S ∈ (Icc (-3 : ℤ) 3).powerset := mem_powerset.mpr hS
  revert S hS hdiam h_univ
  decide

lemma simple_graph_cycle_power_three_layer_weight_fiber_le (n : ℕ) [NeZero n] (hn : 10 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 3).Adj u v)
    (ℓ : ZMod n) :
    ∑ i ∈ univ.filter (fun x => c x = ℓ),
      (2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0)) ≤
      #(univ.filter (fun x => c x = ℓ)) := by
  set K := univ.filter (fun x => c x = ℓ)
  by_cases hK : K.Nonempty
  · obtain ⟨m, hm_mem⟩ := hK
    have hm : c m = ℓ := (mem_filter.mp hm_mem).2
    set S : Finset ℤ := (Icc (-3 : ℤ) 3).filter (fun (e : ℤ) => c (m + (e : ZMod n)) = ℓ)
    have hS_sub : S ⊆ Icc (-3 : ℤ) 3 := filter_subset _ _
    have h_mem : ∀ z, c z = ℓ → ∃ e : ℤ, e ∈ Icc (-3 : ℤ) 3 ∧ z = m + (e : ZMod n) := by
      intro z hz
      by_cases hzm : z = m
      · refine ⟨0, by simp, by simp [hzm]⟩
      · have hadj : (simple_graph_cycle_power n 3).Adj m z := hc m z (Ne.symm hzm) (by rw [hm, hz])
        obtain ⟨e, he0, he3, rfl⟩ := (simple_graph_cycle_power_three_adj_iff n hn m z).mp hadj
        rw [abs_le] at he3
        refine ⟨e, by simp [he3], rfl⟩
    have h_diam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 3 := by
      intro a ha b hb
      have ha_icc : a ∈ Icc (-3 : ℤ) 3 := (mem_filter.mp ha).1
      have hb_icc : b ∈ Icc (-3 : ℤ) 3 := (mem_filter.mp hb).1
      have hca : c (m + (a : ZMod n)) = ℓ := (mem_filter.mp ha).2
      have hcb : c (m + (b : ZMod n)) = ℓ := (mem_filter.mp hb).2
      by_cases hab : a = b
      · subst hab; simp
      · have hne : m + (a : ZMod n) ≠ m + (b : ZMod n) := by
          intro h
          rw [add_left_cancel_iff] at h
          rw [mem_Icc] at ha_icc hb_icc
          have hlt : |a - b| < n := by rw [abs_lt]; constructor <;> omega
          exact hab ((zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b hlt).mp h)
        have hadj : (simple_graph_cycle_power n 3).Adj (m + (a : ZMod n)) (m + (b : ZMod n)) :=
          hc _ _ hne (by rw [hca, hcb])
        obtain ⟨d, hd0, hd3, hd_eq⟩ := (simple_graph_cycle_power_three_adj_iff n hn _ _).mp hadj
        rw [mem_Icc] at ha_icc hb_icc
        rw [abs_le] at hd3
        have h_diff : |b - (a + d)| < n := by
          rw [abs_lt]; constructor <;> omega
        have h_eq' : ((b : ℤ) : ZMod n) = (((a + d : ℤ) : ZMod n)) := by
          have hd_eq' : m + (b : ZMod n) = m + ((a + d : ℤ) : ZMod n) := by
            calc m + (b : ZMod n) = m + (a : ZMod n) + (d : ZMod n) := hd_eq
            _ = m + (((a + d : ℤ) : ZMod n)) := by push_cast; ring
          exact add_left_cancel hd_eq'
        have hbd : b = a + d := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n b (a + d) h_diff).mp h_eq'
        rw [hbd]
        have : a - (a + d) = -d := by ring
        rw [this, abs_neg, abs_le]
        exact ⟨by omega, by omega⟩
    have h_shift : ∀ e ∈ S, ∀ (k : ℤ), k = 2 ∨ k = 3 →
        (c (m + (e : ZMod n) + (k : ZMod n)) = ℓ ↔ e + k ∈ S) := by
      intro e he k hk
      have he_icc : e ∈ Icc (-3 : ℤ) 3 := (mem_filter.mp he).1
      have hk_cast : m + (e : ZMod n) + (k : ZMod n) = m + ((e + k : ℤ) : ZMod n) := by
        push_cast; ring
      rw [hk_cast, mem_filter]
      constructor
      · intro hc_shift
        refine ⟨?_, hc_shift⟩
        obtain ⟨e', he', he'_eq⟩ := h_mem (m + ((e + k : ℤ) : ZMod n)) hc_shift
        have he_eq' : ((e + k : ℤ) : ZMod n) = ((e' : ℤ) : ZMod n) := add_left_cancel he'_eq
        rw [mem_Icc] at he_icc he'
        have hdiff : |(e + k) - e'| < n := by
          rw [abs_lt]
          rcases hk with rfl | rfl <;> omega
        have hek_eq : e + k = e' := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (e + k) e' hdiff).mp he_eq'
        rw [hek_eq]
        exact mem_Icc.mpr he'
      · rintro ⟨h1, h2⟩
        exact h2
    have h_card : #S = #K := by
      apply card_bij (fun (e : ℤ) _ => m + (e : ZMod n))
      · intro e he
        rw [mem_filter]
        exact ⟨mem_univ _, (mem_filter.mp he).2⟩
      · intro e₁ he₁ e₂ he₂ heq
        rw [add_left_cancel_iff] at heq
        have he₁' : e₁ ∈ Icc (-3 : ℤ) 3 := hS_sub he₁
        have he₂' : e₂ ∈ Icc (-3 : ℤ) 3 := hS_sub he₂
        rw [mem_Icc] at he₁' he₂'
        have hdiff : |e₁ - e₂| < n := by
          rw [abs_lt]; constructor <;> omega
        exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n e₁ e₂ hdiff).mp heq
      · intro b hb
        rw [mem_filter] at hb
        obtain ⟨e, he_icc, he_eq⟩ := h_mem b hb.2
        refine ⟨e, mem_filter.mpr ⟨he_icc, ?_⟩, he_eq.symm⟩
        rw [← he_eq]; exact hb.2
    set g := fun (i : ZMod n) =>
      2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0)
    set f := fun (e : ℤ) =>
      2 * (if e + 3 ∈ S then 1 else 0) + (if e + 2 ∈ S then 1 else 0)
    have h_sum : ∑ i ∈ K, g i = simple_graph_cycle_power_three_layer_weight_int_weight S := by
      have h_bij : ∑ e ∈ S, f e = ∑ i ∈ K, g i := by
        apply sum_bij (fun (e : ℤ) _ => m + (e : ZMod n))
        · intro e he
          rw [mem_filter]
          exact ⟨mem_univ _, (mem_filter.mp he).2⟩
        · intro e₁ he₁ e₂ he₂ heq
          rw [add_left_cancel_iff] at heq
          have he₁' : e₁ ∈ Icc (-3 : ℤ) 3 := hS_sub he₁
          have he₂' : e₂ ∈ Icc (-3 : ℤ) 3 := hS_sub he₂
          rw [mem_Icc] at he₁' he₂'
          have hdiff : |e₁ - e₂| < n := by
            rw [abs_lt]; constructor <;> omega
          exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n e₁ e₂ hdiff).mp heq
        · intro b hb
          rw [mem_filter] at hb
          obtain ⟨e, he_icc, he_eq⟩ := h_mem b hb.2
          refine ⟨e, mem_filter.mpr ⟨he_icc, ?_⟩, he_eq.symm⟩
          rw [← he_eq]; exact hb.2
        · intro e he
          have he_c : c (m + (e : ZMod n)) = ℓ := (mem_filter.mp he).2
          have h3_cast : (3 : ZMod n) = ((3 : ℤ) : ZMod n) := by push_cast; rfl
          have h2_cast : (2 : ZMod n) = ((2 : ℤ) : ZMod n) := by push_cast; rfl
          have h3 : (c (m + (e : ZMod n)) = c (m + (e : ZMod n) + 3)) ↔ e + 3 ∈ S := by
            rw [he_c, eq_comm, h3_cast]
            exact h_shift e he 3 (Or.inr rfl)
          have h2 : (c (m + (e : ZMod n)) = c (m + (e : ZMod n) + 2)) ↔ e + 2 ∈ S := by
            rw [he_c, eq_comm, h2_cast]
            exact h_shift e he 2 (Or.inl rfl)
          dsimp [f, g]
          rw [if_congr h3 rfl rfl, if_congr h2 rfl rfl]
      rw [← h_bij]
      rfl
    rw [h_sum, ← h_card]
    exact simple_graph_cycle_power_three_layer_weight_decide_diam S hS_sub h_diam
  · rw [not_nonempty_iff_eq_empty] at hK
    rw [hK]
    simp

theorem simple_graph_cycle_power_three_layer_weight_le (n : ℕ) [NeZero n] (hn : 10 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 3).Adj u v) :
    ∑ i : ZMod n, (2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0)) ≤ n := by
  have h_fiber := sum_fiberwise (s := univ) c
    (fun i => 2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0))
  rw [← h_fiber]
  have h_le : (∑ j : ZMod n, ∑ i with c i = j,
      (2 * (if c i = c (i + 3) then 1 else 0) + (if c i = c (i + 2) then 1 else 0))) ≤
      ∑ j : ZMod n, #{i | c i = j} := by
    apply sum_le_sum
    intro ℓ _
    exact simple_graph_cycle_power_three_layer_weight_fiber_le n hn c hc ℓ
  have h_card : (∑ j : ZMod n, #{i | c i = j}) = n := by
    have := card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := c) (fun _ _ => mem_univ _)
    rw [← this, card_univ, ZMod.card]
  omega
