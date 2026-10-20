import AFTD.Prelude

/-!
# edges_ord_within

Topic: combinatorics   Node: 9cbbf2d7245d

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1271

For a simple graph G and a finite subset S of vertices, the number of directed edges (ordered pairs of distinct adjacent vertices) spanned by S.
-/

/-- Number of ordered pairs of distinct adjacent vertices within a subset S. -/
noncomputable def edges_ord_within {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  letI : DecidableRel G.Adj := Classical.decRel _
  (S.offDiag.filter (fun p => G.Adj p.1 p.2)).card
