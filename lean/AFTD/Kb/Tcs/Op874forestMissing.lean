import AFTD.Prelude
import AFTD.Kb.Tcs.Op874forestEnds
import AFTD.Kb.Tcs.Op874forestColors

/-!
# op874forest_missing

Topic: graphs   Node: d4f9c68deb70

Provenance: helper lemma. OP-874: ten-vertex forest fixed-color obstruction, experiments 38417–38419.

The vertices missing a given external color in the ten-vertex obstruction.
-/

def op874forest_missing (z : Fin 6) : Finset (Fin 10) :=
  Finset.univ.filter fun v => ∀ e : Fin 15, v ∈ op874forest_ends e → op874forest_colors e ≠ z
