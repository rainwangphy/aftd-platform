import AFTD.Prelude

/-!
# digraph_dijoin

Topic: graphs   Node: 6508b882aa64

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 (definition of the dijoin).

The dijoin D₁ → D₂: disjoint copies of D₁ and D₂ together with every arc from a vertex of D₁ to a vertex of D₂.
-/

/-- The dijoin `D₁ → D₂`: disjoint copies of `D₁` and `D₂` with every arc from a vertex
of `D₁` to a vertex of `D₂`. -/
def digraph_dijoin {V W : Type*} (D₁ : Digraph V) (D₂ : Digraph W) : Digraph (V ⊕ W) where
  Adj
    | .inl a, .inl b => D₁.Adj a b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False
    | .inr a, .inr b => D₂.Adj a b
