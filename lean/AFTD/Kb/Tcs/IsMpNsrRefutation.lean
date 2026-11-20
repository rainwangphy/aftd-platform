import AFTD.Prelude
import AFTD.Kb.Tcs.MpNsrEntry
import AFTD.Kb.Tcs.IsContradictoryTropicalPair
import AFTD.Kb.Tcs.MpNsrPremiseTerms
import AFTD.Kb.Tcs.CnfLit

/-!
# is_mp_nsr_refutation

Topic: proof_complexity   Node: 290a023d348d

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 2.3 & Def 2.7

An MP-NSR certificate cert : List (MpNsrEntry n F) is a refutation of a CNF formula F : List (List (CnfLit (Fin n))) over Fin n if the tropical polynomials formed by flat-mapping over each entry e the shifted premise terms (e.coeff + c', fun l => e.monomial l + m' l) for the left-hand and right-hand sides satisfy is_contradictory_tropical_pair n.
-/

/-- An MP-NSR certificate refutes F if its combined tropical inequality is contradictory. -/
def is_mp_nsr_refutation (n : ℕ) (F : List (List (CnfLit (Fin n)))) (cert : List (MpNsrEntry n F)) : Prop := is_contradictory_tropical_pair n
    (cert.flatMap (fun e =>
      (mp_nsr_premise_terms n F e.premise).1.map (fun (c', m') =>
        (e.coeff + c', fun l => e.monomial l + m' l))))
    (cert.flatMap (fun e =>
      (mp_nsr_premise_terms n F e.premise).2.map (fun (c', m') =>
        (e.coeff + c', fun l => e.monomial l + m' l))))
