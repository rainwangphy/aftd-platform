import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinset
import AFTD.Kb.Tcs.WordMinFactorCoveragesSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.PeriodDoublingWord
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.WordFactorCoverages

/-!
# period_doubling_min_factor_coverages_three_card

Topic: combinatorics   Node: bd1737bfbb75

Provenance: original. Related work: arXiv:2610.10950; arXiv:2602.16152

The cardinality of the set of inclusion-minimal factor coverages of the third period-doubling word w_3, period_doubling_min_factor_coverages_finset 3, is equal to 6.
-/

open List

def period_doubling_min_factor_coverages_three_card_factor_coverages_finset
    {α : Type*} [DecidableEq α] (w : List α) : Finset (Finset ℕ) :=
  ((Finset.range w.length).biUnion (fun i =>
    (Finset.Icc 1 (w.length - i)).image (fun k =>
      word_occurrence_coverage w ((w.drop i).take k))))

lemma period_doubling_min_factor_coverages_three_card_mem_word_factor_coverages_iff
    {α : Type*} [DecidableEq α] (w : List α) (C : Finset ℕ) :
    C ∈ word_factor_coverages w ↔
      C ∈ period_doubling_min_factor_coverages_three_card_factor_coverages_finset w := by
  constructor
  · rintro ⟨x, hx, hinf, rfl⟩
    rcases hinf with ⟨s, t, rfl⟩
    have hlen : 1 ≤ x.length := by
      cases x
      · contradiction
      · simp
    rw [period_doubling_min_factor_coverages_three_card_factor_coverages_finset, Finset.mem_biUnion]
    refine ⟨s.length, ?_, ?_⟩
    · rw [Finset.mem_range, length_append, length_append]; omega
    · rw [Finset.mem_image]
      refine ⟨x.length, ?_, ?_⟩
      · rw [Finset.mem_Icc, length_append, length_append]; omega
      · rw [append_assoc, drop_left, take_left]
  · rw [period_doubling_min_factor_coverages_three_card_factor_coverages_finset, Finset.mem_biUnion]
    rintro ⟨i, hi, hC⟩
    rw [Finset.mem_range] at hi
    rw [Finset.mem_image] at hC
    rcases hC with ⟨k, hk, rfl⟩
    rw [Finset.mem_Icc] at hk
    refine ⟨(w.drop i).take k, ?_, ?_, rfl⟩
    · intro hnil
      have : ((w.drop i).take k).length = 0 := by rw [hnil, length_nil]
      rw [length_take, length_drop] at this; omega
    · have h1 : (w.drop i).take k <+: w.drop i := take_prefix k (w.drop i)
      have h2 : w.drop i <:+ w := drop_suffix i w
      exact h1.isInfix.trans h2.isInfix

def period_doubling_min_factor_coverages_three_card_min_factor_coverages_computable
    {α : Type*} [DecidableEq α] (w : List α) : Finset (Finset ℕ) :=
  let H := period_doubling_min_factor_coverages_three_card_factor_coverages_finset w
  H.filter (fun C => ∀ D ∈ H, D ⊆ C → D = C)

lemma period_doubling_min_factor_coverages_three_card_mem_word_min_factor_coverages_iff
    {α : Type*} [DecidableEq α] (w : List α) (C : Finset ℕ) :
    C ∈ word_min_factor_coverages w ↔
      C ∈ period_doubling_min_factor_coverages_three_card_min_factor_coverages_computable w := by
  dsimp [word_min_factor_coverages, period_doubling_min_factor_coverages_three_card_min_factor_coverages_computable]
  rw [Finset.mem_filter]
  rw [period_doubling_min_factor_coverages_three_card_mem_word_factor_coverages_iff]
  constructor
  · rintro ⟨hC, hmin⟩
    refine ⟨hC, ?_⟩
    intro D hD hsub
    apply hmin D
    · rwa [period_doubling_min_factor_coverages_three_card_mem_word_factor_coverages_iff]
    · exact hsub
  · rintro ⟨hC, hmin⟩
    refine ⟨hC, ?_⟩
    intro D hD hsub
    apply hmin D
    · rwa [← period_doubling_min_factor_coverages_three_card_mem_word_factor_coverages_iff]
    · exact hsub

lemma period_doubling_min_factor_coverages_three_card_eq :
    period_doubling_min_factor_coverages_finset 3 =
      period_doubling_min_factor_coverages_three_card_min_factor_coverages_computable (period_doubling_word 3) := by
  classical
  ext C
  dsimp [period_doubling_min_factor_coverages_finset]
  rw [Finset.mem_filter, Finset.mem_powerset, decide_eq_true_eq]
  rw [period_doubling_min_factor_coverages_three_card_mem_word_min_factor_coverages_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hC : C ∈ word_min_factor_coverages (period_doubling_word 3) := by
      rwa [period_doubling_min_factor_coverages_three_card_mem_word_min_factor_coverages_iff]
    have hcov := word_min_factor_coverages_subset (period_doubling_word 3) hC
    rcases hcov with ⟨x, _, _, rfl⟩
    exact word_occurrence_coverage_subset (period_doubling_word 3) x

/-- The number of inclusion-minimal factor coverages of the 3rd period-doubling word w_3 is 6. -/
theorem period_doubling_min_factor_coverages_three_card :
    (period_doubling_min_factor_coverages_finset 3).card = 6 := by
  rw [period_doubling_min_factor_coverages_three_card_eq]
  decide
