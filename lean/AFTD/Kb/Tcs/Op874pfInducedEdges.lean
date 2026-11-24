import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges

/-!
# op874pf_induced_edges

Topic: graphs   Node: 671a12abfd0d

Provenance: helper lemma. OP-874: explicit fixed-external-color obstruction.

The increasing ordered pairs representing the edges induced by a vertex set in the obstruction.
-/

def op874pf_induced_edges (S : Finset (Fin 8)) : Finset (Fin 8 × Fin 8) := Finset.univ.filter fun p : Fin 8 × Fin 8 =>
    p.1 < p.2 ∧ s(p.1,p.2) ∈ op874pf_edges ∧ p.1 ∈ S ∧ p.2 ∈ S
