import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAcyclic

/-!
# digraph_is_acyclic_of_rank

Topic: graphs   Node: a39f71ba26fc

Provenance: helper lemma. Sanity lemma for digraph_is_acyclic (arXiv:2610.13798).

A digraph with a numbering of the vertices that increases along every arc is acyclic.
-/

theorem digraph_is_acyclic_of_rank {V : Type*} (D : Digraph V) (f : V → ℕ)
    (hf : ∀ x y, D.Adj x y → f x < f y) : digraph_is_acyclic D := by
  intro x hx
  have key : ∀ a b, Relation.TransGen D.Adj a b → f a < f b := by
    intro a b hab
    induction hab with
    | single h => exact hf _ _ h
    | tail _ h ih => exact lt_trans ih (hf _ _ h)
  exact lt_irrefl _ (key x x hx)
