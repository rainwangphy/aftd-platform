import AFTD.Prelude

/-!
# is_connection_set

Topic: combinatorics   Node: be6b7465b75b

Provenance: formalization of a published result. Source: arXiv:2611.26732 (connected Cayley approximation of power graphs of finite groups), definition of ρ(G) before Theorem 1.3.

A finite subset S of a group G is a connection set if it does not contain the identity, is closed under inverses (s ∈ S implies s⁻¹ ∈ S), and is nonempty: the sets S over which the unrestricted intersection density ρ(G) is maximised (the paper excludes the empty set to avoid dividing by zero).
-/

def is_connection_set (G : Type*) [Group G] (S : Finset G) : Prop :=
  (1 : G) ∉ S ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧ S.Nonempty
