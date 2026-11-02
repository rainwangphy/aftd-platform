import AFTD.Prelude

/-!
# digraph_common_predecessor_graph

Topic: graphs   Node: e4ea0ab6185f

Provenance: helper lemma. Auxiliary graph in arXiv:2610.11517, Proposition 4.3, and the four-cycle minimum-counterexample route.

The simple graph joining distinct vertices that have a common in-neighbor in the digraph.
-/

def digraph_common_predecessor_graph {α : Type} (D : Digraph α) : SimpleGraph α := {
  Adj := fun u v => u ≠ v ∧ ∃ w, D.Adj w u ∧ D.Adj w v
  symm := by
    constructor
    intro u v h
    obtain ⟨hne, w, hwu, hwv⟩ := h
    exact ⟨hne.symm, w, hwv, hwu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl
}
