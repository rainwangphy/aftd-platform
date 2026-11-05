import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# op_983_dnf_family

Topic: proof_complexity   Node: ad4a50db6f0a

Provenance: helper lemma. step towards op_983_exists_asymptotic_separation_witness

The explicit separating DNF family: over the variables Fin n, one all-positive full-subset term for every subset S of Fin n, together with one extra empty term. (A term is a list of literals; the term for S is the conjunction of all positive literals in S, so it is satisfied exactly by the assignments true on S.)
-/

/-- The candidate separating family A_n: all-positive full-subset terms over Fin n, plus one empty term. -/
noncomputable def op_983_dnf_family (n : ℕ) : List (List (CnfLit (Fin n))) := ((Finset.univ : Finset (Finset (Fin n))).toList.map (fun S => S.toList.map CnfLit.pos)) ++ [[]]
