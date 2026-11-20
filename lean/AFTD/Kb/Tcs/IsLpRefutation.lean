import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.IsLpDerivation
import AFTD.Kb.Tcs.CnfLit

/-!
# is_lp_refutation

Topic: proof_complexity   Node: 2ab09f978b66

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 4.2

A Lift & Project refutation of a CNF formula F : Finset (Finset (CnfLit (Fin n))) is an L&P derivation π : List (LinIneq n) from F containing a contradiction line whose coefficients are all zero and whose constant term is at least 1.
-/

/-- A Lift & Project (L&P) refutation of a CNF formula F derives the contradiction 0 ≥ 1. -/
def is_lp_refutation (n : ℕ) (F : Finset (Finset (CnfLit (Fin n)))) (π : List (LinIneq n)) : Prop :=
  is_lp_derivation n F π ∧ ∃ k : Fin π.length, (∀ j, π[k].coeffs j = 0) ∧ 1 ≤ π[k].const
