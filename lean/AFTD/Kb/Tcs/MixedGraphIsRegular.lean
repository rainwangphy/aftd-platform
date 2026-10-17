import AFTD.Prelude

/-!
# mixed_graph_is_regular

Topic: graphs   Node: fbf843da45f9

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Sec. 2 ((r,z)-regular, also called totally regular).

A mixed graph is (r, z)-regular when every vertex has r neighbours along edges, z out-neighbours and z in-neighbours along arcs.
-/

/-- `(E, A)` is `(r, z)`-regular: every vertex has degree `r` in `E`, out-degree `z` and in-degree `z` in `A` (cardinalities as `Set.ncard`, meant for finite `V`). -/
def mixed_graph_is_regular {V : Type*} (E : SimpleGraph V) (A : V → V → Prop) (r z : ℕ) : Prop :=
  ∀ x, {y | E.Adj x y}.ncard = r ∧ {y | A x y}.ncard = z ∧ {y | A y x}.ncard = z
