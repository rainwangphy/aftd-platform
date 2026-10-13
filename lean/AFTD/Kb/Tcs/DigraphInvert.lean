import AFTD.Prelude

/-!
# digraph_invert

Topic: graphs   Node: eff9dddeca65

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 (definition of the inversion of X in D).

The inversion of a vertex set X in a digraph D: the digraph obtained by reversing every arc with both endpoints in X and keeping every other arc.
-/

/-- Inversion of a vertex set `X` in a digraph: every arc with both endpoints in `X`
is reversed, every other arc is kept. -/
def digraph_invert {V : Type*} (D : Digraph V) (X : Set V) : Digraph V where
  Adj x y := (x ∈ X ∧ y ∈ X ∧ D.Adj y x) ∨ (¬ (x ∈ X ∧ y ∈ X) ∧ D.Adj x y)
