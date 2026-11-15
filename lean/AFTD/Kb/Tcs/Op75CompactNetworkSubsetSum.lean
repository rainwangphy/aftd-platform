import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactNetwork
import AFTD.Kb.Tcs.Op75CompactBlockEffect
import AFTD.Kb.Tcs.Op75CompactSubsetEquivalence
import AFTD.Kb.Tcs.Op75Run
import AFTD.Kb.Tcs.Op75Subset
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.Op75RunInvariants
import AFTD.Kb.Tcs.Op75NetworkEval
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit

/-!
# op75_compact_network_subset_sum

Topic: np_completeness   Node: 02989309cd57

Provenance: original. Related work: OP-75, arXiv:2610.06092, Remark 5.15; the paper leaves width-three verification on the full unit interval open.

For any finite list of nonnegative integer weights and nonnegative integer target, the explicitly constructed width-three ReLU network has a zero in the unit interval if and only if some subset of the list sums to the target.
-/

theorem op75_compact_network_subset_sum (as : List ℕ) (t : ℕ) : relu_network_has_unit_interval_zero (op75_compact_network as t) ↔ op75_subset (as.map fun a => (a : ℝ)) (t : ℝ) := by
  have htyped : relu_network_has_unit_interval_zero (op75_compact_network as t) ↔
      op75_subset (as.map fun a : ℕ => (a:ℝ)) (t:ℝ) := by
    rw [← op75_compact_subset_equivalence]
    unfold relu_network_has_unit_interval_zero
    constructor
    · rintro ⟨x,hx,hzero⟩
      have hq := op75_run_invariants as x hx
      rw [op75_network_eval as t x hx] at hzero
      have habs := abs_nonneg ((op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2 - (t:ℝ))
      have hfirst : (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).1 = 0 := by linarith [hq.1.1]
      have hsecond : (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2 = (t:ℝ) := by
        have : |(op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2 - (t:ℝ)| = 0 := by linarith [hq.1.1]
        exact sub_eq_zero.mp (abs_eq_zero.mp this)
      exact ⟨x,hx,hfirst,hsecond⟩
    · rintro ⟨x,hx,hfirst,hsecond⟩
      refine ⟨x,hx,?_⟩
      rw [op75_network_eval as t x hx,hfirst,hsecond]
      simp
  simpa [← List.map_eq_flatMap, Function.comp_def] using htyped
