import AFTD.Prelude

/-!
# truncated_add_cayley

Topic: combinatorics   Node: 6f99ad68b3c3

Provenance: formalization of a published result. Source: arXiv:2611.05321 Definition 2.1

Given a subset D and a connection set S in an additive abelian group G, the truncated Cayley graph on D with connection set S is the subgraph of the Cayley graph of G with connection set S induced by D.
-/

open scoped Pointwise in
/-- The truncated Cayley graph on vertex set D with connection set S, induced from addCayley S. -/
def truncated_add_cayley {G : Type*} [AddCommGroup G] (D S : Set G) : SimpleGraph D := (SimpleGraph.addCayley S).induce D
