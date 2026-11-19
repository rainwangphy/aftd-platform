import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# eval_thr_lits

Topic: proof_complexity   Node: 468979eda31b

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

The count of literals in a multiset f that evaluate to true under the truth assignment α.
-/

/-- The number of true literals in a multiset under a Boolean assignment. -/
def eval_thr_lits {V : Type*} (α : V → Bool) (f : Multiset (CnfLit V)) : ℕ := (f.filter (fun l => (match l with | CnfLit.pos v => α v | CnfLit.neg v => !α v) = true)).card
