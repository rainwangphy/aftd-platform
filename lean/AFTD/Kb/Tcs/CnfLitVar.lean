import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_lit_var

Topic: proof_complexity   Node: 3117fd3e7bd4

Provenance: formalization of a published result. Source: Short Resolution Refutations for CNFs with Bounded Weighted Incidence Treewidth, arXiv:2610.02047, Sec. 3.1 (variable of a literal)

The variable of a literal: var(x) = var(not x) = x.
-/

/-- The variable of a literal: x for both x and not x. -/
def cnf_lit_var {V : Type*} : CnfLit V → V := fun
  | CnfLit.pos v => v
  | CnfLit.neg v => v
