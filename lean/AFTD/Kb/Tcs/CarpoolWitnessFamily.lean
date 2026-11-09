import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolBackwardStepSlackIncrease
import AFTD.Kb.Tcs.CarpoolEdgeCrosses
import AFTD.Kb.Tcs.CarpoolSlack
import AFTD.Kb.Tcs.CarpoolThresholdA
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# carpool_witness_family

Topic: online_algorithms   Node: b8b2d58eb38e

Provenance: helper lemma. arXiv:2611.00388, Lemma 4.2

Fix n, T, an edge sequence (u_t, v_t) and D >= 300. From the edges alone one builds a family W of pairs (t, S) with |W| <= 2 T 3^ceil(D^2/80), t <= T and 1 <= |S| <= floor(D/40), such that every trajectory of the carpooling discrepancies starting at 0 whose receiving gap is at most 29 at every step and that reaches absolute discrepancy D at a vertex has some (t, S) in W with |d_t(S)| at least D^2/80. This is the witness family of Lemma 4.2 of arXiv:2611.00388.
-/

open Classical in
/-- The witness tree of Lemma 4.2 (2611.00388), read from the edges alone: its leaves. -/
noncomputable def carpool_witness_tree {n : ℕ} (u v : ℕ → Fin n) (K : ℕ) :
    ℕ → Finset (Fin n) → ℕ → Finset (ℕ × Finset (Fin n))
  | 0, S, _ => {(0, S)}
  | t + 1, S, m =>
    if S = ∅ ∨ S.card = K ∨ m = 0 then {(t + 1, S)}
    else if carpool_edge_crosses (u (t + 1)) (v (t + 1)) S then
      carpool_witness_tree u v K t S (m - 1)
        ∪ carpool_witness_tree u v K t (S ∪ {u (t + 1), v (t + 1)}) (m - 1)
        ∪ carpool_witness_tree u v K t (S \ {u (t + 1), v (t + 1)}) (m - 1)
    else carpool_witness_tree u v K t S m

theorem carpool_witness_tree_card {n : ℕ} (u v : ℕ → Fin n) (K : ℕ) :
    ∀ t S m, (carpool_witness_tree u v K t S m).card ≤ 3 ^ m := by
  classical
  intro t
  induction t with
  | zero =>
    intro S m
    simp only [carpool_witness_tree, Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by norm_num)
  | succ t ih =>
    intro S m
    rw [carpool_witness_tree]
    split_ifs with h1 h2
    · simp only [Finset.card_singleton]
      exact Nat.one_le_pow _ _ (by norm_num)
    · have hm : m ≠ 0 := fun h => h1 (Or.inr (Or.inr h))
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have a1 := ih S k
      have a2 := ih (S ∪ {u (t + 1), v (t + 1)}) k
      have a3 := ih (S \ {u (t + 1), v (t + 1)}) k
      have b1 := Finset.card_union_le
        (carpool_witness_tree u v K t S k ∪
          carpool_witness_tree u v K t (S ∪ {u (t + 1), v (t + 1)}) k)
        (carpool_witness_tree u v K t (S \ {u (t + 1), v (t + 1)}) k)
      have b2 := Finset.card_union_le (carpool_witness_tree u v K t S k)
        (carpool_witness_tree u v K t (S ∪ {u (t + 1), v (t + 1)}) k)
      rw [pow_succ]
      omega
    · exact ih S m

theorem carpool_sum_step {n : ℕ} (d d' : Fin n → ℤ) (a b : Fin n) (hab : a ≠ b)
    (hstep : ∀ v, d' v = d v + (if v = a then 1 else if v = b then -1 else 0))
    (S : Finset (Fin n)) :
    ∑ i ∈ S, d' i = ∑ i ∈ S, d i + (if a ∈ S then 1 else 0) - (if b ∈ S then 1 else 0) := by
  classical
  have hsplit : ∀ i : Fin n, (if i = a then (1 : ℤ) else if i = b then -1 else 0)
      = (if i = a then (1 : ℤ) else 0) + (if i = b then (-1 : ℤ) else 0) := by
    intro i
    by_cases h1 : i = a
    · subst h1
      simp [hab]
    · simp [h1]
  simp_rw [hstep, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
  split_ifs <;> simp <;> ring

theorem carpool_child_cases {n : ℕ} (a b u v : Fin n)
    (hor : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) (S S' : Finset (Fin n)) (K : ℕ)
    (hcross : carpool_edge_crosses a b S)
    (hS' : S' = S ∨ S' = insert b S ∨ S' = S \ {a}) (hlt : S.card + 1 ≤ K) :
    (S' = S ∨ S' = S ∪ {u, v} ∨ S' = S \ {u, v}) ∧ S'.card ≤ K := by
  classical
  have hsym1 : ({a, b} : Finset (Fin n)) = {u, v} := by
    rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, Finset.pair_comm]
  have hcard : S'.card ≤ K := by
    rcases hS' with h | h | h
    · rw [h]; omega
    · rw [h]
      have := Finset.card_insert_le b S
      omega
    · rw [h]
      have := Finset.card_le_card (Finset.sdiff_subset (s := S) (t := {a}))
      omega
  refine ⟨?_, hcard⟩
  by_cases haS : a ∈ S
  · have hbS : b ∉ S := by
      unfold carpool_edge_crosses at hcross
      tauto
    rcases hS' with h | h | h
    · exact Or.inl h
    · right; left
      rw [h, ← hsym1]
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro (rfl | hx)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl hx
      · rintro (hx | rfl | rfl)
        · exact Or.inr hx
        · exact Or.inr haS
        · exact Or.inl rfl
    · right; right
      rw [h, ← hsym1]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxa⟩
        refine ⟨hx, ?_⟩
        rintro (rfl | rfl)
        · exact hxa rfl
        · exact hbS hx
      · rintro ⟨hx, hxn⟩
        exact ⟨hx, fun e => hxn (Or.inl e)⟩
  · have hbS : b ∈ S := by
      unfold carpool_edge_crosses at hcross
      tauto
    rcases hS' with h | h | h
    · exact Or.inl h
    · left
      rw [h]
      exact Finset.insert_eq_of_mem hbS
    · left
      rw [h, Finset.sdiff_singleton_eq_erase]
      exact Finset.erase_eq_of_notMem haS

set_option maxHeartbeats 1000000 in
theorem carpool_witness_walk {n : ℕ} (T : ℕ) (u v a b : ℕ → Fin n) (d : ℕ → Fin n → ℤ)
    (K l : ℕ) (D : ℤ)
    (hA : ∀ k, 1 ≤ k → k ≤ K → 0 < carpool_threshold_A D k)
    (hAK : (l : ℤ) ≤ carpool_threshold_A D K)
    (hor : ∀ t, 1 ≤ t → t ≤ T → (a t = u t ∧ b t = v t) ∨ (a t = v t ∧ b t = u t))
    (hab : ∀ t, 1 ≤ t → t ≤ T → a t ≠ b t)
    (hstep : ∀ t w, 1 ≤ t → t ≤ T →
      d t w = d (t - 1) w + (if w = a t then 1 else if w = b t then -1 else 0))
    (hgap : ∀ t, 1 ≤ t → t ≤ T → d t (a t) - d t (b t) ≤ 29)
    (h0 : ∀ w, d 0 w = 0) :
    ∀ t, t ≤ T → ∀ (S : Finset (Fin n)) (m : ℕ), S.Nonempty → S.card ≤ K → m ≤ l →
      ((l : ℤ) - m ≤ carpool_slack D (d t) S) →
      ∃ p ∈ carpool_witness_tree u v K t S m, p.1 ≤ t ∧ p.2.Nonempty ∧ p.2.card ≤ K ∧
        (l : ℤ) ≤ ∑ i ∈ p.2, d p.1 i := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ S m hS hSK hm hsl
    exfalso
    have hc : 1 ≤ S.card := Finset.card_pos.2 hS
    have := hA _ hc hSK
    simp only [carpool_slack, h0, Finset.sum_const_zero] at hsl
    have : (0 : ℤ) ≤ (l : ℤ) - m := by omega
    omega
  | succ t ih =>
    intro htT S m hS hSK hm hsl
    have hsl0 : 0 ≤ carpool_slack D (d (t + 1)) S := by omega
    have hsum : ∑ i ∈ S, d (t + 1) i
        = carpool_slack D (d (t + 1)) S + carpool_threshold_A D S.card := by
      simp only [carpool_slack]
      ring
    have hc : 1 ≤ S.card := Finset.card_pos.2 hS
    rw [carpool_witness_tree]
    split_ifs with h1 h2
    · refine ⟨(t + 1, S), Finset.mem_singleton_self _, le_rfl, hS, hSK, ?_⟩
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 hS.ne_empty
      · have : (l : ℤ) ≤ carpool_threshold_A D S.card := by rw [h1]; exact hAK
        show (l : ℤ) ≤ ∑ i ∈ S, d (t + 1) i
        omega
      · have := hA _ hc hSK
        subst h1
        show (l : ℤ) ≤ ∑ i ∈ S, d (t + 1) i
        simp only [Nat.cast_zero, sub_zero] at hsl
        omega
    · push Not at h1
      obtain ⟨hSne, hSKne, hm0⟩ := h1
      have hlt : S.card < K := lt_of_le_of_ne hSK hSKne
      have ht1 : 1 ≤ t + 1 := by omega
      have hab' := hab (t + 1) ht1 htT
      have hor' := hor (t + 1) ht1 htT
      have hcross : carpool_edge_crosses (a (t + 1)) (b (t + 1)) S := by
        rcases hor' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
        · exact h2
        · unfold carpool_edge_crosses at h2 ⊢
          tauto
      obtain ⟨S', hS', hup, hne⟩ := carpool_backward_step_slack_increase n T D d a b hab hstep hgap
        (t + 1) ht1 htT S hS hcross
      simp only [Nat.add_sub_cancel] at hup
      have hne' : S'.Nonempty := hne hsl0
      have hmono : ∀ S'', S' = S'' → S''.card ≤ K → ∃ p ∈ carpool_witness_tree u v K t S'' (m - 1),
          p.1 ≤ t + 1 ∧ p.2.Nonempty ∧ p.2.card ≤ K ∧ (l : ℤ) ≤ ∑ i ∈ p.2, d p.1 i := by
        rintro _ rfl hcard
        obtain ⟨p, hp, hp1, hp2⟩ := ih (by omega) S' (m - 1) hne' hcard (by omega) (by
          have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
          omega)
        exact ⟨p, hp, by omega, hp2⟩
      obtain ⟨hset, hcardS'⟩ := carpool_child_cases (a (t + 1)) (b (t + 1)) (u (t + 1)) (v (t + 1)) hor'
        S S' K hcross hS' hlt
      have hmem : ∀ {p : ℕ × Finset (Fin n)} {x y z : Finset (ℕ × Finset (Fin n))},
          p ∈ x ∨ p ∈ y ∨ p ∈ z → p ∈ x ∪ y ∪ z := by
        intro p x y z h
        simp only [Finset.mem_union]
        tauto
      rcases hset with h | h | h
      · obtain ⟨p, hp, rest⟩ := hmono _ h (h ▸ hcardS')
        exact ⟨p, hmem (Or.inl hp), rest⟩
      · obtain ⟨p, hp, rest⟩ := hmono _ h (h ▸ hcardS')
        exact ⟨p, hmem (Or.inr (Or.inl hp)), rest⟩
      · obtain ⟨p, hp, rest⟩ := hmono _ h (h ▸ hcardS')
        exact ⟨p, hmem (Or.inr (Or.inr hp)), rest⟩
    · have ht1 : 1 ≤ t + 1 := by omega
      have hab' := hab (t + 1) ht1 htT
      have hor' := hor (t + 1) ht1 htT
      have hstep' : ∀ w, d (t + 1) w = d t w
          + (if w = a (t + 1) then 1 else if w = b (t + 1) then -1 else 0) := by
        intro w
        have := hstep (t + 1) w ht1 htT
        simpa only [Nat.add_sub_cancel] using this
      have hs := carpool_sum_step (d t) (d (t + 1)) (a (t + 1)) (b (t + 1)) hab' hstep' S
      have hsame : (if a (t + 1) ∈ S then (1 : ℤ) else 0) = (if b (t + 1) ∈ S then 1 else 0) := by
        have hnc : ¬ carpool_edge_crosses (a (t + 1)) (b (t + 1)) S := by
          rcases hor' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
          · exact h2
          · unfold carpool_edge_crosses at h2 ⊢
            tauto
        unfold carpool_edge_crosses at hnc
        by_cases h3 : a (t + 1) ∈ S <;> by_cases h4 : b (t + 1) ∈ S <;> simp [h3, h4] <;> tauto
      have hsl' : (l : ℤ) - m ≤ carpool_slack D (d t) S := by
        simp only [carpool_slack] at hsl ⊢
        omega
      obtain ⟨p, hp, hp1, hp2⟩ := ih (by omega) S m hS hSK hm hsl'
      exact ⟨p, hp, by omega, hp2⟩

theorem carpool_witness_family {n : ℕ} (T : ℕ) (u v : ℕ → Fin n) (D : ℕ) (hD : 300 ≤ D) :
    ∃ W : Finset (ℕ × Finset (Fin n)),
      W.card ≤ 2 * T * 3 ^ ((D ^ 2 + 79) / 80) ∧
      (∀ p ∈ W, p.1 ≤ T ∧ 1 ≤ p.2.card ∧ p.2.card ≤ D / 40) ∧
      ∀ (a b : ℕ → Fin n) (d : ℕ → Fin n → ℤ),
        (∀ t, 1 ≤ t → t ≤ T → (a t = u t ∧ b t = v t) ∨ (a t = v t ∧ b t = u t)) →
        (∀ t, 1 ≤ t → t ≤ T → a t ≠ b t) →
        (∀ t w, 1 ≤ t → t ≤ T →
          d t w = d (t - 1) w + (if w = a t then 1 else if w = b t then -1 else 0)) →
        (∀ t, 1 ≤ t → t ≤ T → d t (a t) - d t (b t) ≤ 29) →
        (∀ w, d 0 w = 0) →
        (∃ t, t ≤ T ∧ ∃ i, (D : ℤ) ≤ |d t i|) →
        ∃ p ∈ W, (D : ℤ) ^ 2 ≤ 80 * |∑ i ∈ p.2, d p.1 i| := by
  classical
  set K := D / 40 with hK
  set l := (D ^ 2 + 79) / 80 with hl
  have hK1 : 40 * K ≤ D := by omega
  have hK2 : D ≤ 40 * K + 39 := by omega
  have hKpos : 1 ≤ K := by omega
  have hl1 : D ^ 2 ≤ 80 * l := by omega
  have hl2 : 80 * l ≤ D ^ 2 + 79 := by omega
  have hA : ∀ k, 1 ≤ k → k ≤ K → 0 < carpool_threshold_A (D : ℤ) k := by
    intro k hk1 hk2
    unfold carpool_threshold_A
    have hk3 : (k : ℤ) ≥ 1 := by exact_mod_cast hk1
    have hk4 : (40 : ℤ) * k ≤ D := by
      have : 40 * k ≤ D := by omega
      exact_mod_cast this
    have hk5 : (0 : ℤ) < D - 15 * ((k : ℤ) - 1) := by
      have : (D : ℤ) ≥ 300 := by exact_mod_cast hD
      omega
    nlinarith
  have hAK : (l : ℤ) ≤ carpool_threshold_A (D : ℤ) K := by
    unfold carpool_threshold_A
    have e1 : (40 : ℤ) * K ≤ D := by exact_mod_cast hK1
    have e2 : (D : ℤ) ≤ 40 * K + 39 := by exact_mod_cast hK2
    have e3 : (80 : ℤ) * l ≤ (D : ℤ) ^ 2 + 79 := by exact_mod_cast hl2
    have e4 : (D : ℤ) ≥ 300 := by exact_mod_cast hD
    have e5 : (K : ℤ) ≥ 1 := by exact_mod_cast hKpos
    nlinarith [mul_nonneg (sub_nonneg.2 e1) (show (0 : ℤ) ≤ K by omega),
      mul_nonneg (sub_nonneg.2 e2) (show (0 : ℤ) ≤ D by omega),
      mul_nonneg (sub_nonneg.2 e4) (show (0 : ℤ) ≤ D by omega),
      mul_nonneg (sub_nonneg.2 e5) (show (0 : ℤ) ≤ D by omega)]
  let Rt : ℕ → Finset (ℕ × Finset (Fin n)) := fun s =>
    carpool_witness_tree u v K s {u s} l ∪ carpool_witness_tree u v K s {v s} l
  refine ⟨((Finset.Icc 1 T).biUnion Rt).filter
    (fun p => p.1 ≤ T ∧ 1 ≤ p.2.card ∧ p.2.card ≤ K), ?_, ?_, ?_⟩
  · refine (Finset.card_filter_le _ _).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ s ∈ Finset.Icc 1 T, (Rt s).card
        ≤ ∑ _s ∈ Finset.Icc 1 T, 2 * 3 ^ l := by
          refine Finset.sum_le_sum fun s _ => ?_
          have h1 := carpool_witness_tree_card u v K s {u s} l
          have h2 := carpool_witness_tree_card u v K s {v s} l
          have h3 := Finset.card_union_le (carpool_witness_tree u v K s {u s} l)
            (carpool_witness_tree u v K s {v s} l)
          simp only [Rt]
          omega
      _ = 2 * T * 3 ^ l := by
          simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
          ring
  · intro p hp
    exact (Finset.mem_filter.1 hp).2
  · intro a b d hor hab hstep hgap h0 hM
    have hDpos : (0 : ℤ) < D := by
      have : (D : ℤ) ≥ 300 := by exact_mod_cast hD
      omega
    obtain ⟨hex, _⟩ : (∃ t, t ≤ T ∧ ∃ i, (D : ℤ) ≤ |d t i|) ∧ True := ⟨hM, trivial⟩
    let P : ℕ → Prop := fun t => t ≤ T ∧ ∃ i, (D : ℤ) ≤ |d t i|
    have hP : ∃ t, P t := hM
    set s := Nat.find hP with hs
    obtain ⟨hsT, i, hi⟩ : P s := Nat.find_spec hP
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, h0] at hi
      simp at hi
      omega
    have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs0
    have hprev : ∀ j, |d (s - 1) j| < D := by
      intro j
      by_contra hcon
      have : P (s - 1) := ⟨by omega, j, not_lt.1 hcon⟩
      have := Nat.find_min' hP this
      omega
    have hend : i = a s ∨ i = b s := by
      by_contra hcon
      push Not at hcon
      have := hstep s i hs1 hsT
      rw [if_neg hcon.1, if_neg hcon.2, add_zero] at this
      rw [this] at hi
      exact absurd hi (not_le.2 (hprev i))
    have hmemroot : ∀ p, (p ∈ carpool_witness_tree u v K s {i} l) → p ∈ (Finset.Icc 1 T).biUnion Rt := by
      intro p hp
      refine Finset.mem_biUnion.2 ⟨s, Finset.mem_Icc.2 ⟨hs1, hsT⟩, ?_⟩
      simp only [Rt, Finset.mem_union]
      rcases hor s hs1 hsT with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hend with rfl | rfl
      · left; rwa [← e1]
      · right; rwa [← e2]
      · right; rwa [← e1]
      · left; rwa [← e2]
    have hsingle : ∀ e : ℕ → Fin n → ℤ, carpool_slack (D : ℤ) (e s) {i} = e s i - D := by
      intro e
      simp [carpool_slack, carpool_threshold_A]
    have hconclude : ∀ p, p ∈ carpool_witness_tree u v K s {i} l → p.1 ≤ s → p.2.Nonempty →
        p.2.card ≤ K → (l : ℤ) ≤ |∑ j ∈ p.2, d p.1 j| →
        ∃ p ∈ ((Finset.Icc 1 T).biUnion Rt).filter
          (fun p => p.1 ≤ T ∧ 1 ≤ p.2.card ∧ p.2.card ≤ K),
          (D : ℤ) ^ 2 ≤ 80 * |∑ j ∈ p.2, d p.1 j| := by
      intro p hp h1 h2 h3 h4
      refine ⟨p, Finset.mem_filter.2 ⟨hmemroot p hp, by omega, Finset.card_pos.2 h2, h3⟩, ?_⟩
      have : ((D ^ 2 : ℕ) : ℤ) ≤ ((80 * l : ℕ) : ℤ) := by exact_mod_cast hl1
      push_cast at this
      omega
    rcases le_abs'.1 hi with hneg | hpos
    · -- negative: walk on `-d` with the orientation swapped
      have hneg' : (D : ℤ) ≤ - d s i := by omega
      obtain ⟨p, hp, h1, h2, h3, h4⟩ := carpool_witness_walk T u v b a (fun t w => - d t w) K l D hA hAK
        (fun t ht1 ht2 => by
          rcases hor t ht1 ht2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact Or.inr ⟨e2, e1⟩
          · exact Or.inl ⟨e2, e1⟩)
        (fun t ht1 ht2 => (hab t ht1 ht2).symm)
        (fun t w ht1 ht2 => by
          have h := hstep t w ht1 ht2
          have hne := hab t ht1 ht2
          by_cases e1 : w = a t
          · subst e1
            simp [hne, h]
            ring
          · by_cases e2 : w = b t
            · subst e2
              simp [e1, h]
              ring
            · simp [e1, e2, h])
        (fun t ht1 ht2 => by
          have := hgap t ht1 ht2
          omega)
        (fun w => by simp [h0]) s hsT {i} l (Finset.singleton_nonempty i) (by simpa using hKpos) le_rfl
        (by
          have := hsingle (fun t w => - d t w)
          rw [this]
          omega)
      refine hconclude p hp h1 h2 h3 ?_
      have : ∑ j ∈ p.2, - d p.1 j = - ∑ j ∈ p.2, d p.1 j := Finset.sum_neg_distrib ..
      rw [this] at h4
      exact le_trans h4 (neg_le_abs _)
    · obtain ⟨p, hp, h1, h2, h3, h4⟩ := carpool_witness_walk T u v a b d K l D hA hAK hor hab hstep hgap
        h0 s hsT {i} l (Finset.singleton_nonempty i) (by simpa using hKpos) le_rfl (by
          rw [hsingle d]
          omega)
      exact hconclude p hp h1 h2 h3 (le_trans h4 (le_abs_self _))
