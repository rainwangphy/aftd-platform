import AFTD.Prelude
import AFTD.Kb.Tcs.ThrCond
import AFTD.Kb.Tcs.IsThrResDerivation
import AFTD.Kb.Tcs.CnfLit

/-!
# is_thr_res_refutation

Topic: proof_complexity   Node: cf394912fa46

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

A Threshold Resolution refutation of a CNF formula F : Finset (Finset (CnfLit (Fin n))) is a Thr-Res derivation π : List (ThrCond n) from F such that there exists an index k : Fin π.length with for all l, π[k].coeffs l = 0 and 1 ≤ π[k].threshold.
-/

/-- A Threshold Resolution (Thr-Res) refutation of a CNF formula F derives the contradiction 0 ≥ 1. -/
def is_thr_res_refutation (n : ℕ) (F : Finset (Finset (CnfLit (Fin n)))) (π : List (ThrCond n)) : Prop :=
  is_thr_res_derivation n F π ∧ ∃ k : Fin π.length, (∀ l, π[k].coeffs l = 0) ∧ 1 ≤ π[k].threshold
