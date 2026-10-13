import AFTD.Prelude

/-!
# digraph_reverse

Topic: graphs   Node: a408bf9b87ba

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 4 (D̄, the tournament obtained by flipping every arc of D).

The reverse D̄ of a digraph D: the digraph on the same vertices with every arc turned around.
-/

/-- The reverse of a digraph: every arc turned around. -/
def digraph_reverse {V : Type*} (D : Digraph V) : Digraph V where
  Adj x y := D.Adj y x
