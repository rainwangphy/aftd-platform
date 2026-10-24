import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCakeAllocation
import AFTD.Kb.GameTheoryEconomics.IsEqualLengthAllocation
import AFTD.Kb.GameTheoryEconomics.IsPropLbProportional

/-!
# equal_length_proportional_cake_suffix_volume

Topic: fair_division   Node: 149ff395cdc6

Provenance: helper lemma. scout/2610-19733-exact-cut-complexity-of-equal-length-proportional-cake-cutt.md:386

In any equal-length proportional cake allocation C : Fin n → Set ℝ for n ≥ 1 under the identical valuation profile where each agent values only the prefix [0, 1/n], each bundle C i has suffix Lebesgue measure volume (C i ∩ Set.Ioc (1 / n) 1) equal to ENNReal.ofReal (1 / n - 1 / n^2).
-/

/-- In any equal-length proportional allocation under the lower-bound valuation profile, each bundle has suffix volume 1/n - 1/n^2. -/
theorem equal_length_proportional_cake_suffix_volume (n : ℕ) (hn : 1 ≤ n)
    (C : Fin n → Set ℝ)
    (h_alloc : is_cake_allocation n C)
    (h_len : is_equal_length_allocation n C)
    (h_prop : is_prop_lb_proportional n C)
    (i : Fin n) :
    MeasureTheory.volume (C i ∩ Set.Ioc (1 / (n : ℝ)) 1) =
      ENNReal.ofReal (1 / (n : ℝ) - 1 / ((n : ℝ) ^ 2)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  obtain ⟨hmeas, hdisj, hunion⟩ := h_alloc
  have hsub : ∀ i : Fin n, C i ⊆ Set.Icc (0:ℝ) 1 := by
    intro i x hx
    rw [← hunion]
    exact Set.subset_iUnion C i hx
  set q : ℝ := 1 / (n:ℝ) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hnpos]
    exact hn1
  have hSmeas : ∀ i, MeasurableSet (C i ∩ Set.Icc (0:ℝ) q) := fun i => (hmeas i).inter measurableSet_Icc
  have hSdisj : Pairwise (Function.onFun Disjoint (fun i => C i ∩ Set.Icc (0:ℝ) q)) := by
    intro i j hij
    exact (hdisj i j hij).mono Set.inter_subset_left Set.inter_subset_left
  have hSunion : (⋃ i : Fin n, (C i ∩ Set.Icc (0:ℝ) q)) = Set.Icc (0:ℝ) q := by
    rw [← Set.iUnion_inter, hunion]
    exact Set.inter_eq_right.mpr (fun x hx => ⟨hx.1, le_trans hx.2 hq1⟩)
  have hSfin : ∀ i, MeasureTheory.volume (C i ∩ Set.Icc (0:ℝ) q) ≠ ⊤ := by
    intro i
    have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume) (Set.inter_subset_right : C i ∩ Set.Icc (0:ℝ) q ⊆ Set.Icc (0:ℝ) q)
    rw [Real.volume_Icc, sub_zero] at hle
    exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := q)) hle
  have hsum_enn : (∑ i : Fin n, MeasureTheory.volume (C i ∩ Set.Icc (0:ℝ) q)) = ENNReal.ofReal q := by
    have h := MeasureTheory.measure_iUnion (μ := MeasureTheory.volume) hSdisj hSmeas
    rw [hSunion, Real.volume_Icc, sub_zero] at h
    rw [h, tsum_fintype]
  have hsum_real : (∑ i : Fin n, (MeasureTheory.volume (C i ∩ Set.Icc (0:ℝ) q)).toReal) = q := by
    have h := ENNReal.toReal_sum (s := Finset.univ) (f := fun i => MeasureTheory.volume (C i ∩ Set.Icc (0:ℝ) q)) (fun i _ => hSfin i)
    rw [hsum_enn, ENNReal.toReal_ofReal hq0] at h
    simpa using h.symm
  have hc0 : 0 ≤ (1/(n:ℝ))*(1/(n:ℝ)) := by positivity
  have hlower : ∀ j, (1/(n:ℝ))*(1/(n:ℝ)) ≤ (MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q)).toReal := by
    intro j
    have h1 : (1:ENNReal) / (n:ENNReal) ≤ (n:ENNReal) * MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q) := h_prop j
    have htop : (n:ENNReal) * MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (hSfin j)
    have hreal : (1:ℝ) / (n:ℝ) ≤ (n:ℝ) * (MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q)).toReal := by
      have h2 := ENNReal.toReal_mono htop h1
      rwa [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_one, ENNReal.toReal_natCast] at h2
    have hmul := mul_le_mul_of_nonneg_left hreal (show (0:ℝ) ≤ 1/(n:ℝ) by positivity)
    have hsimp : (1/(n:ℝ)) * ((n:ℝ) * (MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q)).toReal) = (MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q)).toReal := by
      field_simp
    rw [hsimp] at hmul
    exact hmul
  have hzero : ∀ j, (MeasureTheory.volume (C j ∩ Set.Icc (0:ℝ) q)).toReal = (1/(n:ℝ))*(1/(n:ℝ)) := by
    intro j
    have hqc : q = (n:ℝ) * ((1/(n:ℝ))*(1/(n:ℝ))) := by
      rw [hq]; field_simp
    have hsc : (∑ _l : Fin n, ((1/(n:ℝ))*(1/(n:ℝ)))) = (n:ℝ) * ((1/(n:ℝ))*(1/(n:ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsum_sub : (∑ l : Fin n, ((MeasureTheory.volume (C l ∩ Set.Icc (0:ℝ) q)).toReal - (1/(n:ℝ))*(1/(n:ℝ)))) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_real, hsc, hqc, sub_self]
    have hnonneg : ∀ l ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ((MeasureTheory.volume (C l ∩ Set.Icc (0:ℝ) q)).toReal - (1/(n:ℝ))*(1/(n:ℝ))) := by
      intro l _
      linarith [hlower l]
    have hfinal := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_sub j (Finset.mem_univ j)
    linarith
  have hVj : MeasureTheory.volume (C i ∩ Set.Icc (0:ℝ) q) = ENNReal.ofReal ((1/(n:ℝ))*(1/(n:ℝ))) := by
    rw [← ENNReal.ofReal_toReal (hSfin i), hzero i]
  have hCeq : C i = (C i ∩ Set.Icc (0:ℝ) q) ∪ (C i ∩ Set.Ioc q 1) := by
    ext x; constructor
    · intro hx
      have hx1 := hsub i hx
      rcases lt_or_ge q x with h | h
      · exact Or.inr ⟨hx, h, hx1.2⟩
      · exact Or.inl ⟨hx, hx1.1, h⟩
    · intro hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
  have hdisj_AB : Disjoint (C i ∩ Set.Icc (0:ℝ) q) (C i ∩ Set.Ioc q 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact absurd hy.2.1 (not_lt.mpr hx.2.2)
  have hmu := MeasureTheory.measure_union (μ := MeasureTheory.volume) hdisj_AB ((hmeas i).inter measurableSet_Ioc)
  rw [← hCeq, h_len i] at hmu
  rw [hVj] at hmu
  have hres := ENNReal.sub_eq_of_eq_add (a := ENNReal.ofReal (1/(n:ℝ)))
      (b := ENNReal.ofReal ((1/(n:ℝ))*(1/(n:ℝ)))) (c := MeasureTheory.volume (C i ∩ Set.Ioc q 1))
      ENNReal.ofReal_ne_top (by rw [add_comm]; exact hmu)
  rw [← hres, hq, ← ENNReal.ofReal_sub (1/(n:ℝ)) (q := (1/(n:ℝ))*(1/(n:ℝ))) hc0]
  congr 1
  field_simp
