import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionIsolatedHeightResidue
import AFTD.Kb.Tcs.MondrianPerfectHeightInjective
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_perfect_width_free_count_ne_two

Topic: combinatorics   Node: b9d2397ed8f2

Provenance: helper lemma. Helper for the remaining three-prime cases of OP-280, arXiv:2610.19193, Section 1; follows from periodic row isolation.

In a perfect admissible square partition, for any divisor d of the square side, exactly two tiles cannot have widths indivisible by d.
-/

theorem mondrian_perfect_width_free_count_ne_two (n d : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) (hdn : d ∣ n) :
    P.countP (fun r => decide (¬ d ∣ mondrian_rect_width r)) ≠ 2 := by
  intro hc
  let cond := fun r => decide (¬ d ∣ mondrian_rect_width r)
  have hc_filt : (P.filter cond).length = 2 := by
    rw [← List.countP_eq_length_filter]
    exact hc
  obtain ⟨r, s, hfilt⟩ := List.length_eq_two.mp hc_filt
  have hmem_iff : ∀ t, (t ∈ P ∧ cond t = true) ↔ t = r ∨ t = s := by
    intro t
    rw [← List.mem_filter, hfilt]
    simp
  have hr_in : r ∈ P := (hmem_iff r).mpr (Or.inl rfl) |>.1
  have hs_in : s ∈ P := (hmem_iff s).mpr (Or.inr rfl) |>.1
  have hr_ndvd : ¬ d ∣ mondrian_rect_width r := by
    have := (hmem_iff r).mpr (Or.inl rfl) |>.2
    simpa [cond] using this
  have hs_ndvd : ¬ d ∣ mondrian_rect_width s := by
    have := (hmem_iff s).mpr (Or.inr rfl) |>.2
    simpa [cond] using this
  have hnodup : P.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    apply hP.2.2.1.imp
    intro a b hab he
    subst b
    exact hab.2 (Or.inl ⟨rfl, rfl⟩)
  have hfilt_nodup : [r, s].Nodup := by
    rw [← hfilt]
    exact hnodup.filter cond
  have hne : r ≠ s := by simpa using hfilt_nodup
  have hne_h : mondrian_rect_height r ≠ mondrian_rect_height s := by
    intro heq
    exact hne (mondrian_perfect_height_injective n P hP hz r hr_in s hs_in heq)
  have h_contra : ∀ u v, u ∈ P → v ∈ P → ¬ d ∣ mondrian_rect_width u →
      (∀ t, (t ∈ P ∧ cond t = true) → t = u ∨ t = v) →
      mondrian_rect_height u < mondrian_rect_height v → False := by
    intro u v hu hv hu_ndvd hall hlt
    have hpos_u := (mondrian_partition_bounds n P hP u hu).2.2.2.1
    have hnot_dvd_v_u : ¬ mondrian_rect_height v ∣ mondrian_rect_height u := by
      intro hdvd
      have := Nat.le_of_dvd hpos_u hdvd
      exact lt_irrefl _ (hlt.trans_le this)
    have hothers : ∀ t ∈ P, t ≠ u → d ∣ mondrian_rect_width t ∨ mondrian_rect_height v ∣ mondrian_rect_height t := by
      intro t ht htu
      by_cases hdt : d ∣ mondrian_rect_width t
      · exact Or.inl hdt
      · have hcond : cond t = true := by
          simpa [cond] using hdt
        have ht_or := hall t ⟨ht, hcond⟩
        rcases ht_or with rfl | rfl
        · exact (htu rfl).elim
        · exact Or.inr dvd_rfl
    have hdvd_u := mondrian_partition_isolated_height_residue n d (mondrian_rect_height v) P hP hdn u hu hnot_dvd_v_u hothers
    exact hu_ndvd hdvd_u
  rcases lt_or_gt_of_ne hne_h with hlt | hgt
  · exact h_contra r s hr_in hs_in hr_ndvd (fun t ht => (hmem_iff t).mp ht) hlt
  · have hall_symm : ∀ t, (t ∈ P ∧ cond t = true) → t = s ∨ t = r := by
      intro t ht
      rcases (hmem_iff t).mp ht with h | h
      · exact Or.inr h
      · exact Or.inl h
    exact h_contra s r hs_in hr_in hs_ndvd hall_symm hgt
