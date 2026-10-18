import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# simple_graph_cycle_power_seven_layer_weight_le

Topic: combinatorics   Node: 5920bb22b2e7

Provenance: helper lemma. step toward the k = 7 case of OP-205 (arXiv:2610.15635), research thread RT-1, case k = 7 (k + 1 = 8): the weights (w_4, w_6, w_7) = (1, 1, 2) are the unique half-integral optimum of the class LP, with value 4 (exp 1084)

Let n ≥ 22 and let c label the vertices of C_n^7 so that every label class is a clique. Then Σ_i (2·[i ~ i+7] + [i ~ i+6] + [i ~ i+4]) ≤ n, where i ~ j means same class: each class K contributes 2·(pairs at distance 7) + (pairs at distance 6) + (pairs at distance 4) ≤ |K|.
-/

open Finset

def simple_graph_cycle_power_seven_layer_weight_int_weight (T : Finset ℤ) : ℕ :=
  ∑ e ∈ T, (2 * (if e + 7 ∈ T then 1 else 0) + (if e + 6 ∈ T then 1 else 0) + (if e + 4 ∈ T then 1 else 0))

theorem simple_graph_cycle_power_seven_layer_weight_decide_256 :
    ∀ S ∈ (Icc (0 : ℤ) 7).powerset, simple_graph_cycle_power_seven_layer_weight_int_weight S ≤ #S := by
  decide

lemma simple_graph_cycle_power_seven_layer_weight_int_weight_map_add (T : Finset ℤ) (d : ℤ) :
    simple_graph_cycle_power_seven_layer_weight_int_weight (T.map (addRightEmbedding d)) =
      simple_graph_cycle_power_seven_layer_weight_int_weight T := by
  unfold simple_graph_cycle_power_seven_layer_weight_int_weight
  rw [sum_map]
  simp only [addRightEmbedding_apply]
  congr 1
  ext e
  have h1 : e + d + 7 ∈ T.map (addRightEmbedding d) ↔ e + 7 ∈ T := by
    rw [mem_map]
    simp only [addRightEmbedding_apply]
    constructor
    · rintro ⟨a, ha, h⟩
      have : a = e + 7 := by omega
      subst this; exact ha
    · intro h; exact ⟨e + 7, h, by omega⟩
  have h2 : e + d + 6 ∈ T.map (addRightEmbedding d) ↔ e + 6 ∈ T := by
    rw [mem_map]
    simp only [addRightEmbedding_apply]
    constructor
    · rintro ⟨a, ha, h⟩
      have : a = e + 6 := by omega
      subst this; exact ha
    · intro h; exact ⟨e + 6, h, by omega⟩
  have h3 : e + d + 4 ∈ T.map (addRightEmbedding d) ↔ e + 4 ∈ T := by
    rw [mem_map]
    simp only [addRightEmbedding_apply]
    constructor
    · rintro ⟨a, ha, h⟩
      have : a = e + 4 := by omega
      subst this; exact ha
    · intro h; exact ⟨e + 4, h, by omega⟩
  simp only [h1, h2, h3]

lemma simple_graph_cycle_power_seven_layer_weight_le_card_of_diam (S : Finset ℤ)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 7) :
    simple_graph_cycle_power_seven_layer_weight_int_weight S ≤ #S := by
  by_cases hne : S.Nonempty
  · set m := S.min' hne
    have hm : m ∈ S := min'_mem S hne
    set S' := S.map (addRightEmbedding (-m))
    have hS' : S' ⊆ Icc 0 7 := by
      intro x hx
      rw [mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      simp only [addRightEmbedding_apply, mem_Icc]
      have h1 : m ≤ y := min'_le S y hy
      have h2 : |y - m| ≤ 7 := hdiam y hy m hm
      constructor
      · omega
      · rw [abs_of_nonneg (by omega)] at h2
        omega
    have h_le := simple_graph_cycle_power_seven_layer_weight_decide_256 S' (mem_powerset.mpr hS')
    rw [simple_graph_cycle_power_seven_layer_weight_int_weight_map_add S (-m)] at h_le
    rw [card_map] at h_le
    exact h_le
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    unfold simple_graph_cycle_power_seven_layer_weight_int_weight
    simp

lemma simple_graph_cycle_power_seven_layer_weight_fiber_le (n : ℕ) [NeZero n] (hn : 22 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 7).Adj u v)
    (ℓ : ZMod n) :
    ∑ i ∈ univ.filter (fun x => c x = ℓ),
      (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
        + (if c i = c (i + 4) then 1 else 0)) ≤
      #(univ.filter (fun x => c x = ℓ)) := by
  set K := univ.filter (fun x => c x = ℓ)
  by_cases hK : K.Nonempty
  · rcases hK with ⟨m, hm⟩
    have hcm : c m = ℓ := (mem_filter.mp hm).2
    set S : Finset ℤ := (Icc (-7 : ℤ) 7).filter (fun e => c (m + (e : ZMod n)) = ℓ)
    have hsurj : ∀ u ∈ K, ∃ e ∈ S, m + (e : ZMod n) = u := by
      intro u hu
      rw [mem_filter] at hu
      by_cases hum : u = m
      · subst hum; use 0; refine ⟨?_, by simp⟩
        rw [mem_filter, mem_Icc]; refine ⟨by omega, by simp [hcm]⟩
      · have hadj := hc m u (Ne.symm hum) (by rw [hu.2, hcm])
        rw [simple_graph_cycle_power_seven_adj_iff n hn] at hadj
        rcases hadj with ⟨e', -, he'_le, he'_eq⟩
        use e'
        have he'_Icc : e' ∈ Icc (-7 : ℤ) 7 := by
          rw [mem_Icc]
          rcases abs_cases e' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        refine ⟨?_, he'_eq.symm⟩
        rw [mem_filter]; refine ⟨he'_Icc, ?_⟩
        rw [← he'_eq, hu.2]
    have hinj : ∀ e1 ∈ S, ∀ e2 ∈ S, m + (e1 : ZMod n) = m + (e2 : ZMod n) → e1 = e2 := by
      intro e1 he1 e2 he2 h
      have heq : (e1 : ZMod n) = (e2 : ZMod n) := add_left_cancel h
      have he1_Icc := (mem_filter.mp he1).1
      have he2_Icc := (mem_filter.mp he2).1
      rw [mem_Icc] at he1_Icc he2_Icc
      have hnZ : (22 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      have hdiff : |e1 - e2| < (n : ℤ) := by
        rcases abs_cases (e1 - e2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n e1 e2 hdiff).mp heq
    have h_diam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 7 := by
      intro a ha b hb
      have ha_Icc := (mem_filter.mp ha).1
      have hb_Icc := (mem_filter.mp hb).1
      rw [mem_Icc] at ha_Icc hb_Icc
      by_cases hab : a = b
      · subst hab; simp
      · have hnZ : (22 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        have hdiff_ab : |a - b| < (n : ℤ) := by
          rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        have hne : m + (a : ZMod n) ≠ m + (b : ZMod n) := by
          intro h
          apply hab
          exact hinj a ha b hb h
        have hadj := hc (m + (a : ZMod n)) (m + (b : ZMod n)) hne (by
          rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2])
        rw [simple_graph_cycle_power_seven_adj_iff n hn] at hadj
        rcases hadj with ⟨e, -, he_le, he_eq⟩
        have heq : ((b - a : ℤ) : ZMod n) = (e : ZMod n) := by
          calc ((b - a : ℤ) : ZMod n)
            _ = (b : ZMod n) - (a : ZMod n) := by push_cast; rfl
            _ = (m + (b : ZMod n)) - (m + (a : ZMod n)) := by ring
            _ = (m + (a : ZMod n) + (e : ZMod n)) - (m + (a : ZMod n)) := by rw [he_eq]
            _ = (e : ZMod n) := by ring
        have he_cases : -7 ≤ e ∧ e ≤ 7 := by
          rcases abs_cases e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        have hdiff_sub : |(b - a) - e| < (n : ℤ) := by
          rcases abs_cases ((b - a) - e) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        have he_eq2 : b - a = e :=
          (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (b - a) e hdiff_sub).mp heq
        rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have h_shift : ∀ (d : ℤ) (_ : 0 ≤ d) (_ : d ≤ 7) (e : ℤ) (he_in_S : e ∈ S),
        c (m + (e : ZMod n)) = c (m + (e : ZMod n) + (d : ZMod n)) ↔ e + d ∈ S := by
      intro d hd_ge hd_le e he_in_S
      have he := mem_filter.mp he_in_S
      constructor
      · intro h
        have h_target : c (m + (e : ZMod n) + (d : ZMod n)) = ℓ := by
          rw [← h]; exact he.2
        have hu_in_K : m + (e : ZMod n) + (d : ZMod n) ∈ K := by
          rw [mem_filter]; exact ⟨mem_univ _, h_target⟩
        rcases hsurj (m + (e : ZMod n) + (d : ZMod n)) hu_in_K with ⟨e', he', he'_eq⟩
        have heq_mod : (((e + d : ℤ) : ZMod n) : ZMod n) = (e' : ZMod n) := by
          have : m + (((e + d : ℤ) : ZMod n)) = m + (e' : ZMod n) := by
            calc m + (((e + d : ℤ) : ZMod n))
              _ = m + (e : ZMod n) + (d : ZMod n) := by push_cast; ring
              _ = m + (e' : ZMod n) := he'_eq.symm
          exact add_left_cancel this
        have he_Icc := he.1
        have he'_Icc := (mem_filter.mp he').1
        rw [mem_Icc] at he_Icc he'_Icc
        have hnZ : (22 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        have hdiff : |(e + d) - e'| < (n : ℤ) := by
          rcases abs_cases ((e + d) - e') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        have heq_int : e + d = e' :=
          (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (e + d) e' hdiff).mp heq_mod
        subst heq_int
        exact he'
      · intro hed
        have hed_val := (mem_filter.mp hed).2
        have h1 : c (m + (e : ZMod n)) = ℓ := he.2
        have h2 : c (m + (e : ZMod n) + (d : ZMod n)) = ℓ := by
          have : m + (e : ZMod n) + (d : ZMod n) = m + ((e + d : ℤ) : ZMod n) := by
            push_cast; ring
          rw [this, hed_val]
        rw [h1, h2]
    have h_sum : ∑ i ∈ K, (2 * (if c i = c (i + 7) then 1 else 0) +
        (if c i = c (i + 6) then 1 else 0) + (if c i = c (i + 4) then 1 else 0)) =
        simple_graph_cycle_power_seven_layer_weight_int_weight S := by
      unfold simple_graph_cycle_power_seven_layer_weight_int_weight
      have h_bij := sum_bij (s := S) (t := K)
        (f := fun e => 2 * (if e + 7 ∈ S then 1 else 0) + (if e + 6 ∈ S then 1 else 0) + (if e + 4 ∈ S then 1 else 0))
        (g := fun i => 2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0) + (if c i = c (i + 4) then 1 else 0))
        (fun e _ => m + (e : ZMod n))
        (by intro e he; rw [mem_filter]; exact ⟨mem_univ _, (mem_filter.mp he).2⟩)
        (by intro e1 he1 e2 he2 heq; exact hinj e1 he1 e2 he2 heq)
        (by intro u hu; rcases hsurj u hu with ⟨e, he, he_eq⟩; exact ⟨e, he, he_eq⟩)
        (by
          intro e he
          have h7 := h_shift 7 (by omega) (by omega) e he
          have h6 := h_shift 6 (by omega) (by omega) e he
          have h4 := h_shift 4 (by omega) (by omega) e he
          rw [if_congr h7.symm rfl rfl]
          rw [if_congr h6.symm rfl rfl]
          rw [if_congr h4.symm rfl rfl]
          push_cast
          rfl)
      exact h_bij.symm
    have h_card : #K = #S := by
      have := card_bij (s := S) (t := K) (fun e _ => m + (e : ZMod n))
        (by intro e he; rw [mem_filter]; exact ⟨mem_univ _, (mem_filter.mp he).2⟩)
        (by intro e1 he1 e2 he2 heq; exact hinj e1 he1 e2 he2 heq)
        (by intro u hu; rcases hsurj u hu with ⟨e, he, he_eq⟩; exact ⟨e, he, he_eq⟩)
      exact this.symm
    rw [h_sum, h_card]
    exact simple_graph_cycle_power_seven_layer_weight_le_card_of_diam S h_diam
  · rw [not_nonempty_iff_eq_empty] at hK
    rw [hK, sum_empty, card_empty]

theorem simple_graph_cycle_power_seven_layer_weight_le (n : ℕ) [NeZero n] (hn : 22 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 7).Adj u v) :
    ∑ i : ZMod n, (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
      + (if c i = c (i + 4) then 1 else 0)) ≤ n := by
  have h_fiber := sum_fiberwise (s := univ) c
    (fun i => 2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
      + (if c i = c (i + 4) then 1 else 0))
  rw [← h_fiber]
  have h_le : (∑ j : ZMod n, ∑ i with c i = j,
      (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
        + (if c i = c (i + 4) then 1 else 0))) ≤
      ∑ j : ZMod n, #{i | c i = j} := by
    apply sum_le_sum
    intro ℓ _
    exact simple_graph_cycle_power_seven_layer_weight_fiber_le n hn c hc ℓ
  have h_card : (∑ j : ZMod n, #{i | c i = j}) = n := by
    have := card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := c) (fun _ _ => mem_univ _)
    rw [← this, card_univ, ZMod.card]
  omega
