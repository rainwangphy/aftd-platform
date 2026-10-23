import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_lit_compl

Topic: proof_complexity   Node: b6a038a1c651

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

The complement of a literal, negating its polarity.
-/

/-- The complementary literal: `compl (pos v) = neg v` and `compl (neg v) = pos v`. -/
def cnf_lit_compl {V : Type*} : CnfLit V → CnfLit V := fun l => match l with | CnfLit.pos v => CnfLit.neg v | CnfLit.neg v => CnfLit.pos v
