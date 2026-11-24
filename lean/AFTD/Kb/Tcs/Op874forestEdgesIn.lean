import AFTD.Prelude
import AFTD.Kb.Tcs.Op874forestEnds

/-!
# op874forest_edges_in

Topic: graphs   Node: 8a2a4d683c7e

Provenance: helper lemma. OP-874: ten-vertex forest fixed-color obstruction, experiments 38417–38419.

The indexed edges induced by a given vertex set in the ten-vertex obstruction.
-/

def op874forest_edges_in (S : Finset (Fin 10)) : Finset (Fin 15) :=
  Finset.univ.filter fun e => ∃ u ∈ S, ∃ v ∈ S, op874forest_ends e = s(u,v)
