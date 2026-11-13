import AFTD.Prelude

/-!
# expand_vertex

Topic: quantum_mechanics   Node: 3f0139b47ff4

Provenance: original. Related work: folklore

Given a graph J on vertex type V and a marked vertex s, the vertex expansion replaces s by an independent set of new vertices W, each adjacent to exactly the neighbors of s in J.
-/

/-- The simple graph obtained from J by replacing vertex s with an independent set W of vertices having the same neighborhood as s. -/
def expand_vertex {V W : Type*} (J : SimpleGraph V) (s : V) :
    SimpleGraph ({v : V // v ≠ s} ⊕ W) := {
  Adj := fun x y => match x, y with
    | Sum.inl u, Sum.inl v => J.Adj u.val v.val
    | Sum.inl u, Sum.inr _ => J.Adj u.val s
    | Sum.inr _, Sum.inl v => J.Adj s v.val
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (u | w) (v | z) h
    · exact J.adj_symm h
    · change J.Adj s u.val; exact J.adj_symm h
    · change J.Adj v.val s; exact J.adj_symm h
    · contradiction⟩
  loopless := ⟨by
    rintro (u | w) h
    · exact J.loopless.irrefl u.val h
    · contradiction⟩
}
