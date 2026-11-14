import AFTD.Prelude

/-!
# digraph_18_target_core

Topic: graphs   Node: 11b975cceb84

Provenance: helper lemma. step towards digraph_18_shared_target_forces_two_cycles

The twelve vertices P ∪ R ∪ Z = {5, 6, 7} ∪ {9, …, 15} ∪ {16, 17}, i.e. the vertices of value at least five with the shared target 8 left out.
-/

/-- The core vertex set P ∪ R ∪ Z: vertices of value at least 5 other than the shared target 8. -/
def digraph_18_target_core : Finset (Fin 18) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val ≠ 8
