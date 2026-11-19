import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfLitCompl

/-!
# ThrResDerivable

Topic: proof_complexity   Node: 26d187c484e9

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

Inductive derivation relation ThrResDerivable F f s for a CNF formula F : List (List (CnfLit V)) (a list of clauses, each a list of literals over V), asserting that a threshold condition f ≥ s (with f : Multiset (CnfLit V) and s : ℤ) is derivable from F, with constructors: source deriving ThrResDerivable F 0 0; clause deriving ThrResDerivable F (f + ↑C) (s + 1) from ThrResDerivable F f s and C ∈ F; resolution deriving ThrResDerivable F f s from ThrResDerivable F (f + {CnfLit.pos x}) s and ThrResDerivable F (f + {CnfLit.neg x}) s for a variable x : V; weak deriving ThrResDerivable F (f + {l}) s from ThrResDerivable F f s for a literal l : CnfLit V; introduce deriving ThrResDerivable F (f + (l ::ₘ cnf_lit_compl l ::ₘ 0)) (s + 1) from ThrResDerivable F f s for a literal l : CnfLit V; and simplify deriving ThrResDerivable F f (s - 1) from ThrResDerivable F (f + (l ::ₘ cnf_lit_compl l ::ₘ 0)) s for a literal l : CnfLit V.
-/

/-- Inductive predicate for Threshold Resolution derivations from a CNF formula. -/
inductive ThrResDerivable {V : Type*} (F : List (List (CnfLit V))) : Multiset (CnfLit V) → ℤ → Prop | source : ThrResDerivable F 0 0
| clause {f s C} : ThrResDerivable F f s → C ∈ F →
    ThrResDerivable F (f + (C : Multiset (CnfLit V))) (s + 1)
| resolution {f s x} : ThrResDerivable F (f + {CnfLit.pos x}) s →
    ThrResDerivable F (f + {CnfLit.neg x}) s → ThrResDerivable F f s
| weak {f s l} : ThrResDerivable F f s → ThrResDerivable F (f + {l}) s
| introduce {f s l} : ThrResDerivable F f s →
    ThrResDerivable F (f + (l ::ₘ cnf_lit_compl l ::ₘ 0)) (s + 1)
| simplify {f s l} : ThrResDerivable F (f + (l ::ₘ cnf_lit_compl l ::ₘ 0)) s →
    ThrResDerivable F f (s - 1)
