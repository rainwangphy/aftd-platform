import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinset
import AFTD.Kb.Tcs.PeriodDoublingWord
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinsetMem
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordFactorCoverages
import AFTD.Kb.Tcs.WordMinFactorCoverages

/-!
# period_doubling_min_factor_coverages_four_card

Topic: combinatorics   Node: 4dbb3f31ca5a

Provenance: original. Related work: arXiv:2610.10950; arXiv:2602.16152

The cardinality of the set of inclusion-minimal factor coverages of the fourth period-doubling word w_4, period_doubling_min_factor_coverages_finset 4, is equal to 8.
-/

private def period_doubling_min_factor_coverages_four_card_factor_finset
    {α : Type*} [DecidableEq α] (w : List α) : Finset (Finset ℕ) :=
  (Finset.range w.length).biUnion fun i =>
    (Finset.Icc 1 (w.length - i)).image fun k =>
      word_occurrence_coverage w (List.take k (List.drop i w))

private lemma period_doubling_min_factor_coverages_four_card_mem_factor
    {α : Type*} [DecidableEq α] (w : List α) (C : Finset ℕ) :
    C ∈ word_factor_coverages w ↔
      C ∈ period_doubling_min_factor_coverages_four_card_factor_finset w := by
  constructor
  · rintro ⟨x, hxne, ⟨s, t, hst⟩, hcov⟩
    subst hcov
    have hwlen : w.length = s.length + x.length + t.length := by
      rw [← hst, List.length_append, List.length_append]
    have hxpos : 0 < x.length := List.length_pos_iff.mpr hxne
    have htd : List.take x.length (List.drop s.length w) = x := by
      rw [← hst, List.append_assoc, List.drop_left, List.take_left]
    rw [period_doubling_min_factor_coverages_four_card_factor_finset, Finset.mem_biUnion]
    refine ⟨s.length, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · rw [Finset.mem_image]
      refine ⟨x.length, ?_, ?_⟩
      · rw [Finset.mem_Icc]; omega
      · rw [htd]
  · intro hC
    rw [period_doubling_min_factor_coverages_four_card_factor_finset, Finset.mem_biUnion] at hC
    obtain ⟨i, hi, hC⟩ := hC
    rw [Finset.mem_image] at hC
    obtain ⟨k, hk, rfl⟩ := hC
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨List.take k (List.drop i w), ?_, ?_, rfl⟩
    · simp only [ne_eq, List.take_eq_nil_iff, not_or]
      refine ⟨by omega, ?_⟩
      intro h
      have hlen : (List.drop i w).length = 0 := by rw [h]; rfl
      rw [List.length_drop] at hlen
      omega
    · refine ⟨List.take i w, List.drop k (List.drop i w), ?_⟩
      calc List.take i w ++ List.take k (List.drop i w) ++ List.drop k (List.drop i w)
          = List.take i w ++ (List.take k (List.drop i w) ++ List.drop k (List.drop i w)) :=
            List.append_assoc _ _ _
        _ = List.take i w ++ List.drop i w := by rw [List.take_append_drop]
        _ = w := List.take_append_drop i w

private def period_doubling_min_factor_coverages_four_card_min_coverages
    {α : Type*} [DecidableEq α] (w : List α) : Finset (Finset ℕ) :=
  (period_doubling_min_factor_coverages_four_card_factor_finset w).filter
    fun C => ∀ D ∈ period_doubling_min_factor_coverages_four_card_factor_finset w, D ⊆ C → D = C

private lemma period_doubling_min_factor_coverages_four_card_mem_min
    {α : Type*} [DecidableEq α] (w : List α) (C : Finset ℕ) :
    C ∈ word_min_factor_coverages w ↔
      C ∈ period_doubling_min_factor_coverages_four_card_min_coverages w := by
  rw [period_doubling_min_factor_coverages_four_card_min_coverages, Finset.mem_filter]
  constructor
  · rintro ⟨hC, hmin⟩
    refine ⟨(period_doubling_min_factor_coverages_four_card_mem_factor w C).mp hC, ?_⟩
    intro D hD hsub
    exact hmin D ((period_doubling_min_factor_coverages_four_card_mem_factor w D).mpr hD) hsub
  · rintro ⟨hC, hmin⟩
    refine ⟨(period_doubling_min_factor_coverages_four_card_mem_factor w C).mpr hC, ?_⟩
    intro D hD hsub
    exact hmin D ((period_doubling_min_factor_coverages_four_card_mem_factor w D).mp hD) hsub

private lemma period_doubling_min_factor_coverages_four_card_eq :
    period_doubling_min_factor_coverages_finset 4 =
      period_doubling_min_factor_coverages_four_card_min_coverages (period_doubling_word 4) := by
  ext C
  rw [period_doubling_min_factor_coverages_finset_mem]
  exact period_doubling_min_factor_coverages_four_card_mem_min _ _

/-- The number of inclusion-minimal factor coverages of the 4th period-doubling word w_4 is 8. -/
theorem period_doubling_min_factor_coverages_four_card :
    (period_doubling_min_factor_coverages_finset 4).card = 8 := by
  rw [period_doubling_min_factor_coverages_four_card_eq]
  decide
