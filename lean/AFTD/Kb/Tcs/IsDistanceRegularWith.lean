import AFTD.Prelude

/-!
# is_distance_regular_with

Topic: graphs   Node: a5ba75177237

Provenance: formalization of a published result. Source: arXiv:2611.05762, Sec. 3.1

A simple graph G on vertex type V is a distance-regular graph with diameter d : ℕ and intersection parameters b, c : Fin d → ℕ if: G is connected, G.diam = d, for every i : Fin d and all vertices x, y : V, if G.dist x y = i.val then the cardinality (Nat.card) of the subtype of vertices z : V such that G.Adj y z and G.dist x z = i.val + 1 is b i, and for every i : Fin d and all vertices x, y : V, if G.dist x y = i.val + 1 then the cardinality (Nat.card) of the subtype of vertices z : V such that G.Adj y z and G.dist x z = i.val is c i.
-/

/-- A simple graph is distance-regular with diameter d and intersection parameters (b, c) if it is connected, has G.diam = d, and the Nat.card of step-forward and step-backward neighbors depends only on distance. -/
def is_distance_regular_with {V : Type*} (G : SimpleGraph V) (d : ℕ)
    (b c : Fin d → ℕ) : Prop := G.Connected ∧ G.diam = d ∧
  (∀ (i : Fin d) ⦃x y : V⦄, G.dist x y = i.val →
    Nat.card {z : V // G.Adj y z ∧ G.dist x z = i.val + 1} = b i) ∧
  (∀ (i : Fin d) ⦃x y : V⦄, G.dist x y = i.val + 1 →
    Nat.card {z : V // G.Adj y z ∧ G.dist x z = i.val} = c i)
