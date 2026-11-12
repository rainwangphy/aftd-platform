import AFTD.Prelude

/-!
# zero_forcing_step

Topic: graphs   Node: f72265cdd530

Provenance: formalization of a published result. Source: arXiv:2611.13244, Section 1 -- Stabilization of the zero forcing number of generalized Petersen graphs

Given a subset B of vertices in a simple graph G, the next round adds to B all vertices w such that w is the unique neighbor outside B of some vertex x in B.
-/

/-- One round of the zero forcing color change rule: black vertices add all vertices that are the unique white neighbor of some black vertex. -/
def zero_forcing_step {V : Type*} (G : SimpleGraph V) (B : Set V) : Set V := B ∪ {w : V | ∃ x ∈ B, G.neighborSet x \ B = {w}}
