import AFTD.Prelude

/-!
# digraph_suppress_to

Topic: graphs   Node: fbe27960bbca

Provenance: helper lemma. Directed vertex suppression for the oriented twenty-cut profile.

Suppress x into q, retaining all arcs between the remaining vertices and redirecting every arc into x to q, while omitting loops.
-/

def digraph_suppress_to {α : Type} [DecidableEq α] (D : Digraph α) (x q : α) : Digraph {v : α // v ≠ x} := ⟨fun u v => u ≠ v ∧ (D.Adj u.val v.val ∨ (v.val = q ∧ D.Adj u.val x))⟩
