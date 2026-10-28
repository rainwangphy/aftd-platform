import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.CanonicalPermutationAvoidanceOfLocalLemma
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.FiniteProductOneSubLowerBoundByFibres

/-!
# wild_partition_of_resource_bounds

Topic: graphs   Node: 3b0cb9dfe6e9

Provenance: helper lemma. Structural helper for OP-306 / arXiv:2610.22142 Section 6; generalizes the proved triple-block permutation argument to arbitrary rooted blocks. Uses the already proved canonical permutation local lemma, whose source is DOI 10.37236/981, Theorem 1 and Lemma 3.

Let n>0 and let a proper coloring of K_n use the color set Fin n. Fix a partition map b from the vertices onto q blocks, with a specified root in every block. Consider every canonical injective assignment from a union of 1 to floor(q/2) blocks onto a vertex set closed under one color. If the sum of weights (21/20)^d/(n)_d of these indexed events through each domain position and through each range vertex is at most 1/50, there exists a new partition into q rooted blocks in which every used color crosses every proper nonempty union of blocks.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {n q : ℕ}

def wsc_pos (b : Fin n → Fin q) (T : Finset (Fin q)) : Finset (Fin n) :=
  Finset.univ.filter fun v => b v ∈ T

lemma wsc_mem_pos {b : Fin n → Fin q} {v : Fin n} {T : Finset (Fin q)} :
    v ∈ wsc_pos b T ↔ b v ∈ T := by simp [wsc_pos]

noncomputable def wsc_wt (n d : ℕ) : ℝ := (21 / 20 : ℝ)^d / (n.descFactorial d : ℝ)

lemma wsc_wt_nonneg (n d : ℕ) : 0 ≤ wsc_wt n d := by unfold wsc_wt; positivity

open Classical in
@[irreducible] noncomputable def wsc_E (b : Fin n → Fin q)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) :
    Finset (Fin n × Finset (Fin q) × (Fin n → Fin n)) :=
  Finset.univ.filter fun t => 1 ≤ t.2.1.card ∧ t.2.1.card ≤ q / 2 ∧
    (∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧
    w279_closed c t.1 ((wsc_pos b t.2.1).image t.2.2)

lemma wsc_mem_E {b : Fin n → Fin q}
    {c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)}
    {t : Fin n × Finset (Fin q) × (Fin n → Fin n)} :
    t ∈ wsc_E b c ↔ 1 ≤ t.2.1.card ∧ t.2.1.card ≤ q / 2 ∧
    (∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧
    w279_closed c t.1 ((wsc_pos b t.2.1).image t.2.2) := by
  unfold wsc_E
  exact w279_mem_filter_univ

theorem wsc_avoid (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (hn : 0 < n) (b : Fin n → Fin q) (r : Fin q → Fin n) (hr : ∀ t, b (r t) = t)
    (hpos : ∀ p : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50)
    (hvert : ∀ w : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50) :
    ∃ σ : Equiv.Perm (Fin n), ∀ t ∈ wsc_E b c, ∃ v ∈ wsc_pos b t.2.1, σ v ≠ t.2.2 v := by
  classical
  have hmemE : ∀ t ∈ wsc_E b c, 1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧ (∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧
      Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧ w279_closed c t.1 ((wsc_pos b t.2.1).image t.2.2) := by
    intro t ht; exact wsc_mem_E.1 ht
  let D : ↥(wsc_E b c) → Finset (Fin n) := fun j => wsc_pos b j.1.2.1
  let f : ↥(wsc_E b c) → Fin n → Fin n := fun j => j.1.2.2
  let x : ↥(wsc_E b c) → ℝ := fun j => wsc_wt n (D j).card
  have hDcard : ∀ j : ↥(wsc_E b c), 1 ≤ (D j).card ∧ (D j).card ≤ n := by
    intro j
    have ht := hmemE j.1 j.2
    obtain ⟨t, hT⟩ := Finset.card_pos.1 (by omega : 0 < j.1.2.1.card)
    refine ⟨Finset.card_pos.2 ⟨r t, ?_⟩, ?_⟩
    · show r t ∈ wsc_pos b j.1.2.1
      rw [wsc_mem_pos, hr]
      exact hT
    · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hsumI : ∀ (P : (Fin n × Finset (Fin q) × (Fin n → Fin n)) → Prop) [DecidablePred P],
      ∑ j ∈ (Finset.univ : Finset ↥(wsc_E b c)).filter (fun j => P j.1), x j =
        ∑ t ∈ (wsc_E b c).filter P, wsc_wt n (wsc_pos b t.2.1).card := by
    intro P _
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_coe_sort (wsc_E b c) (fun t => if P t then wsc_wt n (wsc_pos b t.2.1).card else 0)
  have hx0 : ∀ j, 0 ≤ x j := fun j => wsc_wt_nonneg n  _
  have hx1 : ∀ j, x j < 1 := by
    intro j
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (by have := hDcard j; omega : 0 < (D j).card)
    have hj : j ∈ (Finset.univ : Finset ↥(wsc_E b c)).filter (fun t => p ∈ wsc_pos b t.1.2.1) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
    have hle := Finset.single_le_sum (a := j) (fun j _ => hx0 j) hj
    rw [hsumI (fun t => p ∈ wsc_pos b t.2.1)] at hle
    exact lt_of_le_of_lt (hle.trans (hpos p)) (by norm_num)
  have hprob : ∀ i, (1 : ℝ) / ((n : ℕ).descFactorial (D i).card : ℝ) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
        ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))), (1 - x j) := by
    intro i
    set d := (D i).card with hd
    set N := Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
      ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))) with hN
    let Fsel : ↥(wsc_E b c) → Fin n ⊕ Fin n := fun j =>
      if h : (D i ∩ D j).Nonempty then Sum.inl (Classical.choose h)
      else if h' : ((D i).image (f i) ∩ (D j).image (f j)).Nonempty then Sum.inr (Classical.choose h')
      else Sum.inl ⟨0, hn⟩
    let S : Finset (Fin n ⊕ Fin n) :=
      (D i).map Function.Embedding.inl ∪ ((D i).image (f i)).map Function.Embedding.inr
    have hNmem : ∀ j ∈ N, (D i ∩ D j).Nonempty ∨ ((D i).image (f i) ∩ (D j).image (f j)).Nonempty := by
      intro j hj
      rw [hN, Finset.mem_filter] at hj
      rw [← Finset.not_disjoint_iff_nonempty_inter, ← Finset.not_disjoint_iff_nonempty_inter]
      exact hj.2.2
    have hfS : ∀ j ∈ N, Fsel j ∈ S := by
      intro j hj
      have h0 := hNmem j hj
      simp only [Fsel]
      split_ifs with h h'
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h)).1, rfl⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h')).1, rfl⟩))
      · exact absurd h0 (by tauto)
    have hmass : ∀ r ∈ S, ∑ j ∈ N.filter (fun j => Fsel j = r), x j ≤ 1 / 50 := by
      intro r _
      rcases r with p | w
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(wsc_E b c)).filter (fun j => p ∈ wsc_pos b j.1.2.1), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              · have := (Finset.mem_inter.1 (Classical.choose_spec h)).2
                rw [Sum.inl.injEq] at hF
                rw [← hF]; exact this
              · exact absurd h0 (by tauto)
          _ = _ := hsumI (fun t => p ∈ wsc_pos b t.2.1)
          _ ≤ _ := hpos p
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(wsc_E b c)).filter
                (fun j => w ∈ (wsc_pos b j.1.2.1).image j.1.2.2), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              have := (Finset.mem_inter.1 (Classical.choose_spec h')).2
              rw [Sum.inr.injEq] at hF
              rw [← hF]; exact this
          _ = _ := hsumI (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2)
          _ ≤ _ := hvert w
    have hfib := finite_product_one_sub_lower_bound_by_fibres N S Fsel x (1 / 50) (by norm_num) (by norm_num)
      (fun j _ => ⟨hx0 j, (hx1 j).le⟩) hfS hmass
    have hcardS : S.card ≤ 2 * d := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_map, Finset.card_map]
      have := Finset.card_image_le (s := D i) (f := f i)
      omega
    have hM : (1 - 1 / 50 : ℝ) ^ (2 * d) ≤ (1 - 1 / 50) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcardS
    have hpos : (0 : ℝ) < ((Nat.descFactorial n d : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.2 (by have := hDcard i; omega)
    change (1 : ℝ) / _ ≤ wsc_wt n d * ∏ j ∈ N, (1 - x j)
    unfold wsc_wt 
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    calc (1 : ℝ) ≤ ((21 / 20 : ℝ) * (1 - 1 / 50) ^ 2) ^ d := one_le_pow₀ (by norm_num)
      _ = (21 / 20 : ℝ) ^ d * (1 - 1 / 50) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
      _ ≤ (21 / 20 : ℝ) ^ d * ∏ j ∈ N, (1 - x j) :=
        mul_le_mul_of_nonneg_left (hM.trans hfib) (by positivity)
  obtain ⟨σ, hσ⟩ := canonical_permutation_avoidance_of_local_lemma n hn D f
    (fun j => Finset.card_pos.1 (by have := hDcard j; omega)) (fun j => (hmemE j.1 j.2).2.2.2.1) x hx0 hx1 hprob
  exact ⟨σ, fun t ht => hσ ⟨t, ht⟩⟩


theorem wsc_upper (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (hn : 0 < n) (b : Fin n → Fin q) (r : Fin q → Fin n) (hr : ∀ t, b (r t) = t)
    (hpos : ∀ p : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50)
    (hvert : ∀ w : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c ≤ n - q := by
  classical
  obtain ⟨σ, hσ⟩ := wsc_avoid c hn b r hr hpos hvert
  have hup := simple_graph_wild_number_le_of_block_cut_condition (n := n) (q := q) hn c
    (fun v => b (σ.symm v)) (fun t => σ (r t)) ?_ ?_
  · exact hup
  · intro t
    simpa only [Equiv.symm_apply_apply] using hr t
  · intro e S hS hSu
    by_contra hcon
    have hno : ∀ u v (huv : u ≠ v), b (σ.symm u) ∈ S → b (σ.symm v) ∉ S →
        c ⟨s(u, v), wild_kn_mem huv⟩ ≠ c e := by
      intro u v huv hu hv hc; exact hcon ⟨u, v, huv, hu, hv, hc⟩
    have hScard : 1 ≤ S.card ∧ S.card ≤ (q - 1) := by
      refine ⟨Finset.card_pos.2 hS, ?_⟩
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ S, hSu⟩)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    set T := if S.card ≤ (q / 2) then S else Finset.univ \ S with hTdef
    have hT : 1 ≤ T.card ∧ T.card ≤ (q / 2) := by
      rw [hTdef]; split_ifs with h
      · omega
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega
    have hTclosed : ∀ u w (huw : u ≠ w), b (σ.symm u) ∈ T →
        c ⟨s(u, w), wild_kn_mem huw⟩ = c e → b (σ.symm w) ∈ T := by
      intro u w huw hu hc
      rw [hTdef] at hu ⊢
      split_ifs at hu ⊢ with h
      · by_contra hw; exact hno u w huw hu hw hc
      · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hu ⊢
        intro hw
        refine hno w u (Ne.symm huw) hw hu ?_
        exact (w279_c_swap c (Ne.symm huw)).trans hc
    let gext : Fin n → Fin n := fun v => if v ∈ wsc_pos b T then σ v else v
    have himg : ∀ u, u ∈ (wsc_pos b T).image gext ↔ b (σ.symm u) ∈ T := by
      intro u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
        simp only [gext, if_pos hv, Equiv.symm_apply_apply]
        exact wsc_mem_pos.1 hv
      · intro hu
        have hu' : σ.symm u ∈ wsc_pos b T := wsc_mem_pos.2 hu
        exact Finset.mem_image.2 ⟨σ.symm u, hu', by simp only [gext, if_pos hu', Equiv.apply_symm_apply]⟩
    have hmem : (c e, T, gext) ∈ wsc_E b c := by
      rw [wsc_mem_E ]
      refine ⟨hT.1, hT.2, ?_, ?_, ?_⟩
      · intro v hv; simp only [gext, if_neg hv]
      · intro a ha b hb hab
        simp only [gext, Finset.mem_coe] at ha hb hab
        rw [if_pos ha, if_pos hb] at hab
        exact σ.injective hab
      · intro u hu w huw hc
        rw [himg] at hu ⊢
        exact hTclosed u w huw hu hc
    obtain ⟨v, hv, hne⟩ := hσ _ hmem
    simp only [gext] at hne
    exact hne (by rw [if_pos hv])

theorem wild_partition_of_resource_bounds {n q : ℕ} (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (hn : 0 < n) (b : Fin n → Fin q) (r : Fin q → Fin n) (hr : ∀ t, b (r t) = t)
    (hpos : ∀ p : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50)
    (hvert : ∀ w : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1 / 50) :
    ∃ (p : Fin n → Fin q) (roots : Fin q → Fin n), (∀ t, p (roots t) = t) ∧
      ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin q)), S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v), wild_kn_mem huv⟩ = c e := by
  classical
  obtain ⟨σ, hσ⟩ := wsc_avoid c hn b r hr hpos hvert
  refine ⟨(fun v => b (σ.symm v)), (fun t => σ (r t)), ?_, ?_⟩
  · intro t
    simpa only [Equiv.symm_apply_apply] using hr t
  · intro e S hS hSu
    by_contra hcon
    have hno : ∀ u v (huv : u ≠ v), b (σ.symm u) ∈ S → b (σ.symm v) ∉ S →
        c ⟨s(u, v), wild_kn_mem huv⟩ ≠ c e := by
      intro u v huv hu hv hc; exact hcon ⟨u, v, huv, hu, hv, hc⟩
    have hScard : 1 ≤ S.card ∧ S.card ≤ (q - 1) := by
      refine ⟨Finset.card_pos.2 hS, ?_⟩
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ S, hSu⟩)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    set T := if S.card ≤ (q / 2) then S else Finset.univ \ S with hTdef
    have hT : 1 ≤ T.card ∧ T.card ≤ (q / 2) := by
      rw [hTdef]; split_ifs with h
      · omega
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega
    have hTclosed : ∀ u w (huw : u ≠ w), b (σ.symm u) ∈ T →
        c ⟨s(u, w), wild_kn_mem huw⟩ = c e → b (σ.symm w) ∈ T := by
      intro u w huw hu hc
      rw [hTdef] at hu ⊢
      split_ifs at hu ⊢ with h
      · by_contra hw; exact hno u w huw hu hw hc
      · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hu ⊢
        intro hw
        refine hno w u (Ne.symm huw) hw hu ?_
        exact (w279_c_swap c (Ne.symm huw)).trans hc
    let gext : Fin n → Fin n := fun v => if v ∈ wsc_pos b T then σ v else v
    have himg : ∀ u, u ∈ (wsc_pos b T).image gext ↔ b (σ.symm u) ∈ T := by
      intro u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
        simp only [gext, if_pos hv, Equiv.symm_apply_apply]
        exact wsc_mem_pos.1 hv
      · intro hu
        have hu' : σ.symm u ∈ wsc_pos b T := wsc_mem_pos.2 hu
        exact Finset.mem_image.2 ⟨σ.symm u, hu', by simp only [gext, if_pos hu', Equiv.apply_symm_apply]⟩
    have hmem : (c e, T, gext) ∈ wsc_E b c := by
      rw [wsc_mem_E ]
      refine ⟨hT.1, hT.2, ?_, ?_, ?_⟩
      · intro v hv; simp only [gext, if_neg hv]
      · intro a ha b hb hab
        simp only [gext, Finset.mem_coe] at ha hb hab
        rw [if_pos ha, if_pos hb] at hab
        exact σ.injective hab
      · intro u hu w huw hc
        rw [himg] at hu ⊢
        exact hTclosed u w huw hu hc
    obtain ⟨v, hv, hne⟩ := hσ _ hmem
    simp only [gext] at hne
    exact hne (by rw [if_pos hv])
