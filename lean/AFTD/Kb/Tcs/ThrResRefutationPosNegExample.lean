import AFTD.Prelude
import AFTD.Kb.Tcs.ThrResDerivable
import AFTD.Kb.Tcs.CnfLit

/-!
# thr_res_refutation_pos_neg_example

Topic: proof_complexity   Node: 142da77c7cd4

Provenance: helper lemma. arXiv:2611.24548 Example 2.15

Sanity check: the CNF formula [[CnfLit.pos 0], [CnfLit.neg 0]] consisting of unit clauses {x₀} and {¬x₀} has a Thr-Res refutation deriving 0 ≥ 1, namely ThrResDerivable [[CnfLit.pos 0], [CnfLit.neg 0]] 0 1.
-/

/-- Sanity check: derivation of contradiction from complementary unit clauses. -/
theorem thr_res_refutation_pos_neg_example : ThrResDerivable [[CnfLit.pos (0 : ℕ)], [CnfLit.neg (0 : ℕ)]] 0 1 := by
  refine ThrResDerivable.resolution (f := (0 : Multiset (CnfLit ℕ))) (s := 1) (x := 0) ?_ ?_
  · exact ThrResDerivable.clause ThrResDerivable.source (by simp)
  · exact ThrResDerivable.clause ThrResDerivable.source (by simp)
