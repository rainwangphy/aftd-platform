import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.IsEf1Goods

/-!
# two_agent_ef1_one_mms

Topic: fair_division   Node: 98739746a2ff

Provenance: original. Related work: arXiv:1403.3700, Section 3

For two agents and any finite set of m indivisible goods with nonnegative additive valuations, there exists a complete allocation that is EF1 and satisfies each agent's exact maximin share.
-/

open Finset

private def two_agent_ef1_one_mms_part {m : ℕ} (S : Finset (Fin m)) : Fin m → Fin 2 :=
  fun x => if x ∈ S then 0 else 1
private lemma two_agent_ef1_one_mms_bundle_part_zero {m : ℕ} (S : Finset (Fin m)) :
    bundle_of (two_agent_ef1_one_mms_part S) 0 = S := by
  ext x; simp only [bundle_of, two_agent_ef1_one_mms_part, Finset.mem_univ, true_and]
  by_cases h : x ∈ S <;> simp [h]
private lemma two_agent_ef1_one_mms_bundle_part_one {m : ℕ} (S : Finset (Fin m)) :
    bundle_of (two_agent_ef1_one_mms_part S) 1 = Finset.univ \ S := by
  ext x; simp only [bundle_of, two_agent_ef1_one_mms_part, Finset.mem_univ, true_and, Finset.mem_sdiff]
  by_cases h : x ∈ S <;> simp [h]
private lemma two_agent_ef1_one_mms_iInf_fin_two (f : Fin 2 → ℝ) :
    (⨅ k : Fin 2, f k) = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (ciInf_le (Finite.bddBelow_range f) 0) (ciInf_le (Finite.bddBelow_range f) 1)
  · apply le_ciInf; intro k; fin_cases k <;> simp
private lemma two_agent_ef1_one_mms_maximin_eq {m : ℕ} (v : Finset (Fin m) → ℝ) :
    maximin_share v 2
      = ⨆ Q : Fin m → Fin 2, min (v (bundle_of Q 0)) (v (bundle_of Q 1)) := by
  unfold maximin_share
  simp only [two_agent_ef1_one_mms_iInf_fin_two]
private lemma two_agent_ef1_one_mms_mmsP_le {m : ℕ} (v : Finset (Fin m) → ℝ)
    (Q : Fin m → Fin 2) :
    min (v (bundle_of Q 0)) (v (bundle_of Q 1)) ≤ maximin_share v 2 := by
  rw [two_agent_ef1_one_mms_maximin_eq]
  exact le_ciSup (Finite.bddAbove_range (fun Q : Fin m → Fin 2 =>
    min (v (bundle_of Q 0)) (v (bundle_of Q 1)))) Q
private lemma two_agent_ef1_one_mms_sum_union {m : ℕ} (w : Fin m → ℝ)
    (S T : Finset (Fin m)) (h : Disjoint S T) :
    additive_valuation w (S ∪ T) = additive_valuation w S + additive_valuation w T := by
  simp only [additive_valuation]; rw [Finset.sum_union h]
private lemma two_agent_ef1_one_mms_sum_erase {m : ℕ} (w : Fin m → ℝ)
    (S : Finset (Fin m)) (g : Fin m) (hg : g ∈ S) :
    additive_valuation w S = additive_valuation w (S.erase g) + w g := by
  simp only [additive_valuation]; rw [← Finset.sum_erase_add S w hg]
private lemma two_agent_ef1_one_mms_sum_insert {m : ℕ} (w : Fin m → ℝ)
    (S : Finset (Fin m)) (g : Fin m) (hg : g ∉ S) :
    additive_valuation w (insert g S) = w g + additive_valuation w S := by
  simp only [additive_valuation]; rw [Finset.sum_insert hg]
private lemma two_agent_ef1_one_mms_nonneg {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g)
    (S : Finset (Fin m)) : 0 ≤ additive_valuation w S := by
  simp only [additive_valuation]; exact Finset.sum_nonneg (fun x _ => hw x)
private lemma two_agent_ef1_one_mms_sum_mono {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g)
    {S T : Finset (Fin m)} (h : S ⊆ T) :
    additive_valuation w S ≤ additive_valuation w T := by
  simp only [additive_valuation]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hw x)
private lemma two_agent_ef1_one_mms_bundle_disjoint {m : ℕ} (P : Fin m → Fin 2) :
    Disjoint (bundle_of P 0) (bundle_of P 1) := by
  rw [show bundle_of P 1 = Finset.univ \ bundle_of P 0 from by
    ext x
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h; rw [h]; decide
    · intro h; exact Fin.eq_one_of_ne_zero (P x) h]
  exact Finset.disjoint_sdiff
private lemma two_agent_ef1_one_mms_bundle_union {m : ℕ} (P : Fin m → Fin 2) :
    bundle_of P 0 ∪ bundle_of P 1 = Finset.univ := by
  rw [show bundle_of P 1 = Finset.univ \ bundle_of P 0 from by
    ext x
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h; rw [h]; decide
    · intro h; exact Fin.eq_one_of_ne_zero (P x) h]
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
private lemma two_agent_ef1_one_mms_maximin_le_half {m : ℕ} (w : Fin m → ℝ) :
    maximin_share (additive_valuation w) 2 ≤ additive_valuation w Finset.univ / 2 := by
  rw [two_agent_ef1_one_mms_maximin_eq]
  apply ciSup_le
  intro Q
  have hsum : additive_valuation w (bundle_of Q 0) + additive_valuation w (bundle_of Q 1)
      = additive_valuation w Finset.univ := by
    rw [← two_agent_ef1_one_mms_sum_union w _ _ (two_agent_ef1_one_mms_bundle_disjoint Q),
        two_agent_ef1_one_mms_bundle_union Q]
  have h1 := min_le_left (additive_valuation w (bundle_of Q 0)) (additive_valuation w (bundle_of Q 1))
  have h2 := min_le_right (additive_valuation w (bundle_of Q 0)) (additive_valuation w (bundle_of Q 1))
  linarith

private lemma two_agent_ef1_one_mms_cut {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g)
    (Q : Fin m → Fin 2)
    (hQ : min (additive_valuation w (bundle_of Q 0)) (additive_valuation w (bundle_of Q 1))
            = maximin_share (additive_valuation w) 2)
    (hlt : additive_valuation w (bundle_of Q 0) < additive_valuation w (bundle_of Q 1)) :
    ∃ g ∈ bundle_of Q 1,
      additive_valuation w ((bundle_of Q 1).erase g) ≤ additive_valuation w (bundle_of Q 0) := by
  set A := bundle_of Q 0 with hA
  set B := bundle_of Q 1 with hB
  set v := additive_valuation w with hv
  have hdisj : Disjoint A B := by rw [hA, hB]; exact two_agent_ef1_one_mms_bundle_disjoint Q
  by_contra hcon
  push_neg at hcon
  have hA0 : 0 ≤ v A := two_agent_ef1_one_mms_nonneg w hw A
  have hBpos : 0 < v B := lt_of_le_of_lt hA0 hlt
  have hBne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with h | h
    · rw [h] at hBpos; simp [hv, additive_valuation] at hBpos
    · exact h
  obtain ⟨g, hgB, hgmax⟩ := Finset.exists_max_image B w hBne
  have hwg : 0 < w g := by
    by_contra h
    push_neg at h
    have hall : ∀ x ∈ B, w x = 0 := by
      intro x hx; have h1 := hgmax x hx; have h2 := hw x; linarith
    have : v B = 0 := by
      simp only [hv, additive_valuation]; exact Finset.sum_eq_zero (fun x hx => hall x hx)
    linarith
  have hErase : v A < v (B.erase g) := hcon g hgB
  have hgA : g ∉ A := by
    intro h; exact (Finset.disjoint_left.mp hdisj h) hgB
  have hAg : v A < v (insert g A) := by
    rw [hv, two_agent_ef1_one_mms_sum_insert w A g hgA]; linarith
  have hsub : B.erase g ⊆ Finset.univ \ (insert g A) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, ?_⟩
    rw [Finset.mem_insert]
    rintro (hxg | hxA)
    · exact hx.1 hxg
    · exact (Finset.disjoint_left.mp hdisj hxA) hx.2
  have hmono : v (B.erase g) ≤ v (Finset.univ \ (insert g A)) :=
    two_agent_ef1_one_mms_sum_mono w hw hsub
  have hminlt : v A < min (v (insert g A)) (v (Finset.univ \ (insert g A))) :=
    lt_min hAg (lt_of_lt_of_le hErase hmono)
  have hmax : maximin_share v 2 = v A := by
    rw [← hQ]; exact min_eq_left (le_of_lt hlt)
  have hle := two_agent_ef1_one_mms_mmsP_le v (two_agent_ef1_one_mms_part (insert g A))
  rw [two_agent_ef1_one_mms_bundle_part_zero, two_agent_ef1_one_mms_bundle_part_one, hmax] at hle
  linarith

private lemma two_agent_ef1_one_mms_swap_zero {m : ℕ} (P : Fin m → Fin 2) :
    bundle_of (fun x => if P x = 0 then (1:Fin 2) else 0) 0 = bundle_of P 1 := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : P x = 0
  · have hp1 : ¬ (P x = 1) := by rw [h]; decide
    simp [h, hp1]
  · have hp1 : P x = 1 := Fin.eq_one_of_ne_zero (P x) h
    simp [h, hp1]
private lemma two_agent_ef1_one_mms_swap_one {m : ℕ} (P : Fin m → Fin 2) :
    bundle_of (fun x => if P x = 0 then (1:Fin 2) else 0) 1 = bundle_of P 0 := by
  ext x
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : P x = 0
  · simp [h]
  · have hne : (if P x = 0 then (1:Fin 2) else 0) ≠ 1 := by simp [h]
    simp [h, hne]

/-- For two agents with nonnegative additive valuations, there exists a complete allocation that is EF1 and achieves each agent's full maximin share. -/
theorem two_agent_ef1_one_mms (m : ℕ)
    (u : Fin 2 → Fin m → ℝ) (hpos : ∀ i g, 0 ≤ u i g) :
    ∃ σ : Fin m → Fin 2,
      is_ef1_goods u σ ∧
      ∀ i : Fin 2, maximin_share (additive_valuation (u i)) 2 ≤
        additive_valuation (u i) (bundle_of σ i) := by
  classical
  obtain ⟨P, -, hPmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m → Fin 2))
    (fun Q => min (additive_valuation (u 0) (bundle_of Q 0)) (additive_valuation (u 0) (bundle_of Q 1)))
    Finset.univ_nonempty
  have hPeq : maximin_share (additive_valuation (u 0)) 2
      = min (additive_valuation (u 0) (bundle_of P 0)) (additive_valuation (u 0) (bundle_of P 1)) := by
    rw [two_agent_ef1_one_mms_maximin_eq]
    apply le_antisymm
    · apply ciSup_le; intro Q; exact hPmax Q (Finset.mem_univ Q)
    · exact le_ciSup (Finite.bddAbove_range (fun Q : Fin m → Fin 2 =>
        min (additive_valuation (u 0) (bundle_of Q 0)) (additive_valuation (u 0) (bundle_of Q 1)))) P
  have hsum1 : additive_valuation (u 1) (bundle_of P 0) + additive_valuation (u 1) (bundle_of P 1)
      = additive_valuation (u 1) Finset.univ := by
    rw [← two_agent_ef1_one_mms_sum_union (u 1) _ _ (two_agent_ef1_one_mms_bundle_disjoint P),
        two_agent_ef1_one_mms_bundle_union P]
  by_cases hchoice : additive_valuation (u 1) (bundle_of P 0) ≤ additive_valuation (u 1) (bundle_of P 1)
  · refine ⟨P, ?_, ?_⟩
    · intro i j
      by_cases hi0 : i = 0
      · subst i
        by_cases hj0 : j = 0
        · subst j; left; exact le_refl _
        · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj0
          subst j
          by_cases hv : additive_valuation (u 0) (bundle_of P 1) ≤ additive_valuation (u 0) (bundle_of P 0)
          · left; exact hv
          · push_neg at hv
            right
            exact two_agent_ef1_one_mms_cut (u 0) (fun g => hpos 0 g) P hPeq.symm hv
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
        subst i
        by_cases hj0 : j = 0
        · subst j; left; exact hchoice
        · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj0; subst j; left; exact le_refl _
    · intro i
      by_cases hi0 : i = 0
      · subst i
        calc maximin_share (additive_valuation (u 0)) 2
            = min (additive_valuation (u 0) (bundle_of P 0)) (additive_valuation (u 0) (bundle_of P 1)) := hPeq
          _ ≤ additive_valuation (u 0) (bundle_of P 0) := min_le_left _ _
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
        subst i
        have hhalf : maximin_share (additive_valuation (u 1)) 2 ≤ additive_valuation (u 1) Finset.univ / 2 :=
          two_agent_ef1_one_mms_maximin_le_half (u 1)
        have hle : additive_valuation (u 1) Finset.univ / 2 ≤ additive_valuation (u 1) (bundle_of P 1) := by
          linarith
        linarith
  · push_neg at hchoice
    let σ : Fin m → Fin 2 := fun x => if P x = 0 then 1 else 0
    have hb0 : bundle_of σ 0 = bundle_of P 1 := two_agent_ef1_one_mms_swap_zero P
    have hb1 : bundle_of σ 1 = bundle_of P 0 := two_agent_ef1_one_mms_swap_one P
    have hQσ : min (additive_valuation (u 0) (bundle_of σ 0)) (additive_valuation (u 0) (bundle_of σ 1))
        = maximin_share (additive_valuation (u 0)) 2 := by
      rw [hb0, hb1, min_comm]; exact hPeq.symm
    refine ⟨σ, ?_, ?_⟩
    · intro i j
      by_cases hi0 : i = 0
      · subst i
        by_cases hj0 : j = 0
        · subst j; left; exact le_refl _
        · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj0
          subst j
          by_cases hv : additive_valuation (u 0) (bundle_of σ 1) ≤ additive_valuation (u 0) (bundle_of σ 0)
          · left; exact hv
          · push_neg at hv
            right
            exact two_agent_ef1_one_mms_cut (u 0) (fun g => hpos 0 g) σ hQσ hv
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
        subst i
        by_cases hj0 : j = 0
        · subst j
          rw [hb0, hb1]; left; linarith
        · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj0; subst j; left; exact le_refl _
    · intro i
      by_cases hi0 : i = 0
      · subst i
        rw [hb0]
        calc maximin_share (additive_valuation (u 0)) 2
            = min (additive_valuation (u 0) (bundle_of P 0)) (additive_valuation (u 0) (bundle_of P 1)) := hPeq
          _ ≤ additive_valuation (u 0) (bundle_of P 1) := min_le_right _ _
      · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
        subst i
        rw [hb1]
        have hhalf : maximin_share (additive_valuation (u 1)) 2 ≤ additive_valuation (u 1) Finset.univ / 2 :=
          two_agent_ef1_one_mms_maximin_le_half (u 1)
        have hle : additive_valuation (u 1) Finset.univ / 2 ≤ additive_valuation (u 1) (bundle_of P 0) := by
          linarith
        linarith
