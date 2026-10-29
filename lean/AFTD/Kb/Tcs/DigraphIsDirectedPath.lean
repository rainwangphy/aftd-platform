import AFTD.Prelude

/-!
# digraph_is_directed_path

Topic: graphs   Node: 659ed062816d

Provenance: formalization of a published result. Source: Bang-Jensen and Gutin, Digraphs: Theory, Algorithms and Applications, 2009

A directed path from u to v in a digraph D is a list of vertices p forming a directed chain in D with no duplicate vertices, starting at u and ending at v.
-/

/-- A directed path in a digraph D is a nodup chain of directed edges from u to v. -/
def digraph_is_directed_path {V : Type*} (D : Digraph V) (p : List V) (u v : V) : Prop := p.IsChain D.Adj ∧ p.Nodup ∧ p.head? = some u ∧ p.getLast? = some v
