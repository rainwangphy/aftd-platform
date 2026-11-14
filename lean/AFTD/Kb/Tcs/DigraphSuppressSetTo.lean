import AFTD.Prelude

/-!
# digraph_suppress_set_to

Topic: graphs   Node: 88e1f78e0bd1

Provenance: helper lemma. Multi-vertex suppression for the oriented twenty-cut equality profile.

Suppress a finite vertex set S into q by retaining arcs between remaining vertices and redirecting predecessors of S to q, omitting loops.
-/

def digraph_suppress_set_to {α : Type} [DecidableEq α] (D : Digraph α) (S : Finset α) (q : α) : Digraph {v : α // v ∉ S} := ⟨fun u v => u ≠ v ∧ (D.Adj u.val v.val ∨ (v.val = q ∧ ∃ x ∈ S, D.Adj u.val x))⟩
