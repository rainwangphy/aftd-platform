import AFTD.Prelude

/-!
# digraph_dist_le

Topic: graphs   Node: bec57c00b7f5

Provenance: original. Related work: folklore

A vertex x reaches y in at most β steps in digraph D if there exists a sequence of vertices starting at x and ending at y of length at most β + 1 where each consecutive pair is adjacent in D.
-/

/-- A vertex x reaches y in at most β steps in digraph D along a directed walk. -/
def digraph_dist_le {W : Type*} (D : Digraph W) (x y : W) (β : ℕ) : Prop := ∃ l : List W, l.head? = some x ∧ l.getLast? = some y ∧ l.length - 1 ≤ β ∧ l.IsChain D.Adj
