import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLitDecidableEq
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_restrict

Topic: proof_complexity   Node: 0528ffe97e16

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

The restriction F|x=b of a CNF formula F: delete every clause containing the literal satisfied by x = b, and in the remaining clauses erase the falsified literal on x.
-/

/-- Restriction of a CNF formula to the variable `x = b`: clauses containing the satisfied literal are deleted, and in the remaining clauses the falsified literal is erased. -/
def cnf_restrict {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) (x : V) (b : Bool) : Finset (Finset (CnfLit V)) := (F.filter (fun C => (if b then CnfLit.pos x else CnfLit.neg x) ∉ C)).image (fun C => C.erase (if b then CnfLit.neg x else CnfLit.pos x))
