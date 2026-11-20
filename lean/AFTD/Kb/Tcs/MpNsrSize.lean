import AFTD.Prelude
import AFTD.Kb.Tcs.MpNsrEntry
import AFTD.Kb.Tcs.CnfLit

/-!
# mp_nsr_size

Topic: proof_complexity   Node: 6b612676c912

Provenance: formalization of a published result. Source: arXiv:2611.24548 Sec 2.1 & Def 2.3

The unary size mp_nsr_size of an MP-NSR certificate cert : List (MpNsrEntry n F) for a CNF formula F : List (List (CnfLit (Fin n))) over Fin n, defined as the length of cert plus the sum over all entries e in cert of e.coeff.num.natAbs + e.coeff.den + (∑ i : Fin n, e.monomial (CnfLit.pos i)) + (∑ i : Fin n, e.monomial (CnfLit.neg i)) + 1.
-/

/-- Unary size of an MP-NSR certificate. -/
def mp_nsr_size {n : ℕ} {F : List (List (CnfLit (Fin n)))} (cert : List (MpNsrEntry n F)) : ℕ := cert.length + (cert.map (fun e =>
    e.coeff.num.natAbs + e.coeff.den + (∑ i : Fin n, e.monomial (CnfLit.pos i)) + (∑ i : Fin n, e.monomial (CnfLit.neg i)) + 1)).sum
