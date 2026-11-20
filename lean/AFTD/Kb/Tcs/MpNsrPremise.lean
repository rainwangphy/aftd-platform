import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# MpNsrPremise

Topic: proof_complexity   Node: 50696616aa5f

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 2.7

The inductive type MpNsrPremise (n : ℕ) (F : List (List (CnfLit (Fin n)))) : Type of premises in an MP-NSR refutation of a CNF formula F : List (List (CnfLit (Fin n))) over Fin n, with six constructors: clause (C : List (CnfLit (Fin n))) (hC : C ∈ F), weak_pos (i : Fin n), weak_neg (i : Fin n), pair_upper (i : Fin n), pair_lower (i : Fin n), and resolution (i : Fin n).
-/

/-- Premises available in an MP-NSR refutation of a CNF formula F over n variables. -/
inductive MpNsrPremise (n : ℕ) (F : List (List (CnfLit (Fin n)))) : Type | clause (C : List (CnfLit (Fin n))) (hC : C ∈ F) : MpNsrPremise n F
  | weak_pos (i : Fin n) : MpNsrPremise n F
  | weak_neg (i : Fin n) : MpNsrPremise n F
  | pair_upper (i : Fin n) : MpNsrPremise n F
  | pair_lower (i : Fin n) : MpNsrPremise n F
  | resolution (i : Fin n) : MpNsrPremise n F
