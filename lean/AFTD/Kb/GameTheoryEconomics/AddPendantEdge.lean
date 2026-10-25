import AFTD.Prelude

/-!
# add_pendant_edge

Topic: combinatorial_games   Node: eef77f63047d

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 5.2

The simple graph obtained from a graph H on vertices W by attaching a new pendant edge at a designated vertex c in W, with the new vertex represented by none.
-/

/-- The graph obtained from H by attaching a new pendant edge at vertex c (represented on vertex type Option W). -/
def add_pendant_edge {W : Type*} (H : SimpleGraph W) (c : W) : SimpleGraph (Option W) := {
  Adj := fun u v => match u, v with
    | some w₁, some w₂ => H.Adj w₁ w₂
    | none, some w => w = c
    | some w, none => w = c
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h
    · contradiction
    · exact (h : v = c)
    · exact (h : u = c)
    · exact H.adj_symm h⟩
  loopless := ⟨by
    rintro (_ | u) h
    · contradiction
    · exact H.loopless.irrefl u h⟩
}
