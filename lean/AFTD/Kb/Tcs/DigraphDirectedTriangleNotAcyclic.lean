import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# digraph_directed_triangle_not_acyclic

Topic: graphs   Node: 564fc9d4e619

Provenance: helper lemma. Sanity lemma for digraph_is_acyclic (arXiv:2610.13798).

The directed triangle 0 → 1 → 2 → 0 is not acyclic.
-/

theorem digraph_directed_triangle_not_acyclic :
    ¬ digraph_is_acyclic (⟨fun x y : ZMod 3 => y = x + 1⟩ : Digraph (ZMod 3)) := by
  intro h
  apply h 0
  exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single rfl) rfl) rfl
