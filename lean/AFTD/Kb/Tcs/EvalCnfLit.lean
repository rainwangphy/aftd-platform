import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# eval_cnf_lit

Topic: proof_complexity   Node: 04df1f4af564

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

Evaluation of a CNF literal under a truth assignment: a positive literal pos v evaluates to α v, and a negative literal neg v evaluates to the negation of α v.
-/

/-- Evaluates a CNF literal under a truth assignment. -/
def eval_cnf_lit {V : Type*} (α : V → Bool) (l : CnfLit V) : Bool := match l with
| CnfLit.pos v => α v
| CnfLit.neg v => !(α v)
