import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphExceptionalVerts
import AFTD.Kb.Tcs.DigraphOutDegree

/-!
# digraph_exceptional_verts_card_le

Topic: graphs   Node: 66d79ccf9de0

Provenance: helper lemma. folklore

For any finite directed graph D on a finite vertex type V with decidable adjacency, the number of exceptional vertices (vertices of out-degree 1) in D is at most the cardinality of V.
-/

/-- The number of exceptional vertices in a finite digraph D on V is at most the total number of vertices |V|. -/
theorem digraph_exceptional_verts_card_le {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] : (digraph_exceptional_verts D).card ≤ Fintype.card V := Finset.card_le_univ _
