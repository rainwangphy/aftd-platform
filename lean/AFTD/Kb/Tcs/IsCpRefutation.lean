import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.IsCpDerivation
import AFTD.Kb.Tcs.CnfLit

/-!
# is_cp_refutation

Topic: proof_complexity   Node: eeaa7bd57210

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 4.1

A Cutting Planes refutation of a CNF formula F : Finset (Finset (CnfLit (Fin n))) is a CP derivation π : List (LinIneq n) from F containing a contradiction line whose coefficients are all zero and whose constant term is at least 1.
-/

/-- A Cutting Planes (CP) refutation of a CNF formula F derives the contradiction 0 ≥ 1. -/
def is_cp_refutation (n : ℕ) (F : Finset (Finset (CnfLit (Fin n)))) (π : List (LinIneq n)) : Prop :=
  is_cp_derivation n F π ∧ ∃ k : Fin π.length, (∀ j, π[k].coeffs j = 0) ∧ 1 ≤ π[k].const
