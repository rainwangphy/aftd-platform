import AFTD.Prelude
import AFTD.Kb.Tcs.BpeMinGreedyUtilityOneEqOptimal
import AFTD.Kb.Tcs.IidGreedyBpeApproxProb
import AFTD.Kb.Tcs.IidWordMeasure
import AFTD.Kb.Tcs.IidBpeSharpFactorBounds
import AFTD.Kb.Tcs.IidBpeSharpFactor
import AFTD.Kb.Tcs.BpeOptimalFullUtility
import AFTD.Kb.Tcs.BpeMinGreedyUtility

/-!
# op_1604_iid_greedy_bpe_budget_one

Topic: algorithms   Node: 81e273599e95

Provenance: formalization of a published result. Source: arXiv:2411.08671 Greedy Byte-Pair Encoding Achieves at Least 0.361 of the Optimal Compression, Section 4.3; open problem OP-1604

Open Problem OP-1604 (budget k = 1 case): For a merge budget of k = 1, every alphabet size q ≥ 2, every strictly positive probability vector p on Fin q summing to 1, and every tolerance ε > 0, the greedy BPE approximation probability iid_greedy_bpe_approx_prob q p 1 N ε tends to 1 as string length N tends to infinity.
-/

/-- The greedy BPE approximation probability tends to 1 for merge budget k = 1. -/
theorem op_1604_iid_greedy_bpe_budget_one
    (q : ℕ) (hq : 2 ≤ q) (p : Fin q → ℝ) (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1)
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun N : ℕ => iid_greedy_bpe_approx_prob q p 1 N ε) Filter.atTop (nhds 1) := by
  -- Each marginal of the i.i.d. product measure is a probability measure.
  have hmarg : MeasureTheory.IsProbabilityMeasure
      (∑ j, ENNReal.ofReal (p j) • MeasureTheory.Measure.dirac (j : Fin q)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.coe_finsetSum]
    simp only [Finset.sum_apply, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    simp only [MeasureTheory.Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
      Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => le_of_lt (hp_pos i)), hp_sum,
      ENNReal.ofReal_one]
  -- For budget k = 1 the approximating event is the whole space, so the probability is 1.
  have hprob : ∀ N : ℕ, iid_greedy_bpe_approx_prob q p 1 N ε = 1 := by
    intro N
    haveI : MeasureTheory.IsProbabilityMeasure (iid_word_measure q N p) := by
      rw [iid_word_measure]
      exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    unfold iid_greedy_bpe_approx_prob
    have huniv : {w : Fin N → Fin q |
        (bpe_min_greedy_utility (List.ofFn fun i => (w i : ℕ)) 1 : ℝ) ≥
          (iid_bpe_sharp_factor - ε) * (bpe_optimal_full_utility (List.ofFn fun i => (w i : ℕ)) 1 : ℝ)}
        = Set.univ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      -- Greedy and optimal agree for one merge.
      rw [bpe_min_greedy_utility_one_eq_optimal]
      have hc : iid_bpe_sharp_factor - ε < 1 := by
        have := iid_bpe_sharp_factor_bounds.2
        linarith
      have hu : (0:ℝ) ≤ (bpe_optimal_full_utility (List.ofFn fun i => (w i : ℕ)) 1 : ℝ) := by
        positivity
      nlinarith
    rw [huniv, MeasureTheory.measure_univ]
    exact ENNReal.toReal_one
  simp only [hprob]
  exact tendsto_const_nhds
