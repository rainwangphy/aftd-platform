import AFTD.Prelude

/-!
# digraph_is_tournament

Topic: graphs   Node: 46ec3b695e4d

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 2.1 (tournaments).

A digraph is a tournament when it has no loops and between any two distinct vertices there is exactly one arc.
-/

/-- A tournament: no loops, and between two distinct vertices exactly one arc. -/
def digraph_is_tournament {V : Type*} (D : Digraph V) : Prop :=
  (∀ x, ¬ D.Adj x x) ∧ ∀ x y, x ≠ y → (D.Adj x y ↔ ¬ D.Adj y x)
