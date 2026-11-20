import AFTD.Prelude
import AFTD.Kb.Tcs.ToroidalKingGraph

/-!
# has_nonattacking_king_lift

Topic: graphs   Node: 1b09467b5306

Provenance: formalization of a published result. Source: scout/2611-22830-independent-sets-in-the-2-token-graph-of-a-cycle-and-kings.md:132

Given a natural number n with [NeZero n] and a family I : Finset { s : Finset (Fin n) // s.card = 2 }, has_nonattacking_king_lift n I asserts that there exists a choice function r : { s : Finset (Fin n) // s.card = 2 } → Fin n such that r e ∈ e.val for all e ∈ I, and for all distinct e₁, e₂ ∈ I the vertices (r e₁, e₁.val.sum id) and (r e₂, e₂.val.sum id) are not adjacent in toroidal_king_graph n.
-/

/-- An independent set of two tokens admits a choice of endpoints producing pairwise nonattacking kings under the sum map. -/
def has_nonattacking_king_lift (n : ℕ) [NeZero n] (I : Finset { s : Finset (Fin n) // s.card = 2 }) : Prop := ∃ r : { s : Finset (Fin n) // s.card = 2 } → Fin n,
    (∀ e ∈ I, r e ∈ e.val) ∧
    ∀ e₁ ∈ I, ∀ e₂ ∈ I, e₁ ≠ e₂ →
      ¬ (toroidal_king_graph n).Adj (r e₁, e₁.val.sum id) (r e₂, e₂.val.sum id)
