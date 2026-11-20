import AFTD.Prelude
import AFTD.Kb.Tcs.MpNsrPremise
import AFTD.Kb.Tcs.CnfLit

/-!
# MpNsrEntry

Topic: proof_complexity   Node: 1b2011136ec3

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 2.3 & Def 2.7

A structure MpNsrEntry (n : ℕ) (F : List (List (CnfLit (Fin n)))) : Type representing an entry in an MP-NSR certificate, with fields coeff : ℚ, monomial : CnfLit (Fin n) → ℕ, and premise : MpNsrPremise n F.
-/

/-- An entry in an MP-NSR certificate. -/
structure MpNsrEntry (n : ℕ) (F : List (List (CnfLit (Fin n)))) : Type where
  coeff : ℚ
  monomial : CnfLit (Fin n) → ℕ
  premise : MpNsrPremise n F
