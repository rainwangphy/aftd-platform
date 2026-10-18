import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenLayerWeightLe
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerSevenAdjIff
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_cycle_power_seven_cover_four_tight

Topic: combinatorics   Node: a40e08f6e2fc

Provenance: helper lemma. step toward the k = 7 case of OP-205 (arXiv:2610.15635), research thread RT-1, case k = 7 (k + 1 = 8); the analogue of simple_graph_cycle_power_three_cover_three_tight

In any cover of C_n^7 (n ≥ 22) by 4 equivalence subgraphs, every pair at distance 7, 6 or 4 is covered by exactly one layer, and every class of every layer contains a pair at distance 7 (so it is spanned by an 8-arc).
-/

open BigOperators Finset

lemma simple_graph_cycle_power_seven_cover_four_tight_decide_tight :
    ∀ S ∈ (Icc (0 : ℤ) 7).powerset,
      S.Nonempty →
      simple_graph_cycle_power_seven_layer_weight_int_weight S = S.card →
      (0 : ℤ) ∈ S ∧ (7 : ℤ) ∈ S := by
  decide

lemma simple_graph_cycle_power_seven_cover_four_tight_eq_diam_tight
    (S : Finset ℤ) (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 7)
    (h_weight_eq : simple_graph_cycle_power_seven_layer_weight_int_weight S = S.card)
    (hne : S.Nonempty) :
    ∃ a ∈ S, a + 7 ∈ S ∧ ∀ x ∈ S, a ≤ x ∧ x ≤ a + 7 := by
  let m := S.min' hne
  have hm := S.min'_mem hne
  let S' := Finset.map (addRightEmbedding (-m)) S
  have hS' : S' ⊆ Icc (0 : ℤ) 7 := by
    intro x hx
    rw [mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simp only [addRightEmbedding_apply, mem_Icc]
    have h1 := S.min'_le y hy
    have h2 := hdiam y hy m hm
    rw [abs_le] at h2
    omega
  have hne' : S'.Nonempty := hne.map
  have h_weight_eq' : simple_graph_cycle_power_seven_layer_weight_int_weight S' = S'.card := by
    rw [simple_graph_cycle_power_seven_layer_weight_int_weight_map_add, card_map, h_weight_eq]
  have h07 := simple_graph_cycle_power_seven_cover_four_tight_decide_tight S'
    (Finset.mem_powerset.mpr hS') hne' h_weight_eq'
  refine ⟨m, hm, ?_, ?_⟩
  · have h7 := h07.2
    rw [mem_map] at h7
    rcases h7 with ⟨y, hy, hy_eq⟩
    simp only [addRightEmbedding_apply] at hy_eq
    have : y = m + 7 := by omega
    subst this
    exact hy
  · intro x hx
    have hx' : x + -m ∈ S' := by
      rw [mem_map]
      exact ⟨x, hx, rfl⟩
    have h_icc := hS' hx'
    rw [mem_Icc] at h_icc
    omega

lemma simple_graph_cycle_power_seven_cover_four_tight_layer_weight_eq_imp (n : ℕ) [NeZero n] (hn : 22 ≤ n)
    (c : ZMod n → ZMod n)
    (hc : ∀ u v, u ≠ v → c u = c v → (simple_graph_cycle_power n 7).Adj u v)
    (heq : ∑ i : ZMod n,
      (2 * (if c i = c (i + 7) then 1 else 0) + (if c i = c (i + 6) then 1 else 0)
        + (if c i = c (i + 4) then 1 else 0)) = n) :
    ∀ i : ZMod n, ∃ d : ℕ, d ≤ 7 ∧ c (i - d) = c (i - d + 7) ∧ c (i - d) = c i := by
  intro i
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
  have h0_in_S : (0 : ℤ) ∈ S := by
    rw [mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by simp⟩
  have hne : S.Nonempty := ⟨0, h0_in_S⟩
  rcases simple_graph_cycle_power_seven_cover_four_tight_eq_diam_tight S hdiam h_weight_eq hne
    with ⟨a, ha, ha7, h_bounds⟩
  have ha_bounds := h_bounds 0 h0_in_S
  have ha_le_0 : a ≤ 0 := ha_bounds.1
  have h_0_le_a7 : 0 ≤ a + 7 := ha_bounds.2
  have h_d_le_7 : (-a).toNat ≤ 7 := by omega
  refine ⟨(-a).toNat, h_d_le_7, ?_, ?_⟩
  · have ha_eq : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have ha_cast : (((-a).toNat : ℕ) : ZMod n) = - (a : ZMod n) := by
      rw [← Int.cast_natCast, ha_eq, Int.cast_neg]
    have ha_mem : c (i + (a : ZMod n)) = c i := (mem_filter.mp ha).2
    have ha7_mem : c (i + ((a + 7 : ℤ) : ZMod n)) = c i := (mem_filter.mp ha7).2
    have h1 : i - (((-a).toNat : ℕ) : ZMod n) = i + (a : ZMod n) := by
      rw [ha_cast, sub_neg_eq_add]
    have h2 : i - (((-a).toNat : ℕ) : ZMod n) + 7 = i + ((a + 7 : ℤ) : ZMod n) := by
      rw [h1]; push_cast; ring
    rw [h2, h1, ha_mem, ha7_mem]
  · have ha_eq : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have ha_cast : (((-a).toNat : ℕ) : ZMod n) = - (a : ZMod n) := by
      rw [← Int.cast_natCast, ha_eq, Int.cast_neg]
    have ha_mem : c (i + (a : ZMod n)) = c i := (mem_filter.mp ha).2
    have h1 : i - (((-a).toNat : ℕ) : ZMod n) = i + (a : ZMod n) := by
      rw [ha_cast, sub_neg_eq_add]
    rw [h1, ha_mem]

theorem simple_graph_cycle_power_seven_cover_four_tight (n : ℕ) [NeZero n] (hn : 22 ≤ n)
    (c : Fin 4 → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v → (simple_graph_cycle_power n 7).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n 7).Adj u v → ∃ s, c s u = c s v) :
    (∀ i, ∃! s, c s i = c s (i + 7)) ∧ (∀ i, ∃! s, c s i = c s (i + 6)) ∧ (∀ i, ∃! s, c s i = c s (i + 4)) ∧
      ∀ s i, ∃ d : ℕ, d ≤ 7 ∧ c s (i - d) = c s (i - d + 7) ∧ c s (i - d) = c s i := by
  open BigOperators Finset in
  have hadj7 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 7) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨7, by decide, by decide, by push_cast; rfl⟩
  have hadj6 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 6) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨6, by decide, by decide, by push_cast; rfl⟩
  have hadj4 : ∀ i : ZMod n, (simple_graph_cycle_power n 7).Adj i (i + 4) := by
    intro i
    rw [simple_graph_cycle_power_seven_adj_iff n hn]
    exact ⟨4, by decide, by decide, by push_cast; rfl⟩
  have hcov7 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 7) := fun i => hcov i (i + 7) (hadj7 i)
  have hcov6 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 6) := fun i => hcov i (i + 6) (hadj6 i)
  have hcov4 : ∀ i : ZMod n, ∃ s : Fin 4, c s i = c s (i + 4) := fun i => hcov i (i + 4) (hadj4 i)

  let W : Fin 4 → ℕ := fun s =>
    ∑ i : ZMod n, (2 * (if c s i = c s (i + 7) then 1 else 0) + (if c s i = c s (i + 6) then 1 else 0)
      + (if c s i = c s (i + 4) then 1 else 0))
  have hW_le : ∀ s : Fin 4, W s ≤ n := fun s =>
    simple_graph_cycle_power_seven_layer_weight_le n hn (c s) (hc s)

  have hsum_le : ∑ s : Fin 4, W s ≤ 4 * n := by
    have h := sum_le_card_nsmul (univ : Finset (Fin 4)) W n (fun s _ => hW_le s)
    simp only [card_univ, Fintype.card_fin] at h
    rw [Nat.nsmul_eq_mul] at h
    exact h

  let N7 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 7) then 1 else 0
  let N6 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 6) then 1 else 0
  let N4 : ZMod n → ℕ := fun i => ∑ s : Fin 4, if c s i = c s (i + 4) then 1 else 0

  have hN7_ge : ∀ i : ZMod n, 1 ≤ N7 i := by
    intro i
    rcases hcov7 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 7) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have hN6_ge : ∀ i : ZMod n, 1 ≤ N6 i := by
    intro i
    rcases hcov6 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 6) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have hN4_ge : ∀ i : ZMod n, 1 ≤ N4 i := by
    intro i
    rcases hcov4 i with ⟨s, hs⟩
    have hle := Finset.single_le_sum (f := fun x => if c x i = c x (i + 4) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ s)
    rwa [if_pos hs] at hle

  have h_term_ge : ∀ i : ZMod n, 4 ≤ 2 * N7 i + N6 i + N4 i := fun i => by
    have := hN7_ge i
    have := hN6_ge i
    have := hN4_ge i
    omega

  have hsum_comm : ∑ s : Fin 4, W s = ∑ i : ZMod n, (2 * N7 i + N6 i + N4 i) := by
    dsimp [W, N7, N6, N4]
    rw [sum_comm]
    congr 1
    ext i
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum]

  have hsum_ge : 4 * n ≤ ∑ s : Fin 4, W s := by
    rw [hsum_comm]
    have h := card_nsmul_le_sum (univ : Finset (ZMod n)) (fun i => 2 * N7 i + N6 i + N4 i) 4 (fun i _ => h_term_ge i)
    have hc : card (univ : Finset (ZMod n)) = n := ZMod.card n
    rw [hc, Nat.nsmul_eq_mul] at h
    omega

  have hsum_eq : ∑ s : Fin 4, W s = 4 * n := by omega
  have hsum_term_eq : ∑ i : ZMod n, (2 * N7 i + N6 i + N4 i) = 4 * n := by omega

  have hW_eq : ∀ s : Fin 4, W s = n := by
    intro s
    have hsum_const : ∑ _s : Fin 4, n = 4 * n := by
      simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    have hle' : ∀ s ∈ (univ : Finset (Fin 4)), W s ≤ (fun _ => n) s := fun s _ => hW_le s
    by_contra hne
    have hlt : W s < n := lt_of_le_of_ne (hW_le s) hne
    have : ∑ x : Fin 4, W x < ∑ _x : Fin 4, n := Finset.sum_lt_sum hle' ⟨s, mem_univ s, hlt⟩
    omega

  have h_term_eq : ∀ i : ZMod n, 2 * N7 i + N6 i + N4 i = 4 := by
    intro i
    have hsum_const : ∑ _i : ZMod n, 4 = 4 * n := by
      have hc : card (univ : Finset (ZMod n)) = n := ZMod.card n
      simp only [sum_const, hc, Nat.nsmul_eq_mul]
      omega
    have hle' : ∀ j ∈ (univ : Finset (ZMod n)), (fun _ => 4) j ≤ 2 * N7 j + N6 j + N4 j := fun j _ => h_term_ge j
    by_contra hne
    have hlt : 4 < 2 * N7 i + N6 i + N4 i := lt_of_le_of_ne (h_term_ge i) (Ne.symm hne)
    have : ∑ _x : ZMod n, 4 < ∑ x : ZMod n, (2 * N7 x + N6 x + N4 x) := Finset.sum_lt_sum hle' ⟨i, mem_univ i, hlt⟩
    omega

  have hN7_eq : ∀ i : ZMod n, N7 i = 1 := by
    intro i
    have := h_term_eq i
    have := hN7_ge i
    have := hN6_ge i
    have := hN4_ge i
    omega

  have hN6_eq : ∀ i : ZMod n, N6 i = 1 := by
    intro i
    have := h_term_eq i
    have := hN7_ge i
    have := hN6_ge i
    have := hN4_ge i
    omega

  have hN4_eq : ∀ i : ZMod n, N4 i = 1 := by
    intro i
    have := h_term_eq i
    have := hN7_ge i
    have := hN6_ge i
    have := hN4_ge i
    omega

  have h_exists_unique : ∀ (P : Fin 4 → Prop) [DecidablePred P],
      (∑ s : Fin 4, (if P s then 1 else 0)) = 1 → ∃! s, P s := by
    intro P _ h
    have hcard : card (filter P univ) = 1 := by
      have h1 : (∑ s : Fin 4, if P s then 1 else 0 : ℕ) = card (filter P univ) := sum_boole (R := ℕ) P univ
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

  refine ⟨fun i => h_exists_unique (fun s => c s i = c s (i + 7)) (hN7_eq i),
          fun i => h_exists_unique (fun s => c s i = c s (i + 6)) (hN6_eq i),
          fun i => h_exists_unique (fun s => c s i = c s (i + 4)) (hN4_eq i),
          fun s i => ?_⟩
  exact simple_graph_cycle_power_seven_cover_four_tight_layer_weight_eq_imp n hn (c s) (hc s) (hW_eq s) i
