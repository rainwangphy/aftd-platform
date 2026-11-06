import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# OneLayeredFamily

Topic: combinatorics   Node: 7f0239615ab3

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 2

Given a type V and a natural number r, a 1-layered family of r-subsets on V is a structure OneLayeredFamily (V : Type*) (r : ℕ) consisting of a positive number k of layers (k : ℕ with 0 < k) indexed by Fin k, where each layer layers t is a nonempty finite set of r-element subsets of V (Finset (Finset V)), the layers are pairwise disjoint (for all t₁ ≠ t₂, layers t₁ and layers t₂ are disjoint), and for every nonempty finite subset S of V (S : Finset V with S.Nonempty), the set of indices t : Fin k for which some member of layers t contains S is order-connected (Set.OrdConnected in Fin k).
-/

/-- A 1-layered family of r-subsets on a vertex type V partitioned into nonempty layers satisfying the interval property. -/
structure OneLayeredFamily (V : Type*) (r : ℕ) where
  k : ℕ
  k_pos : 0 < k
  layers : Fin k → Finset (Finset V)
  layers_nonempty : ∀ t, (layers t).Nonempty
  layers_card : ∀ t, ∀ F ∈ layers t, F.card = r
  layers_disjoint : ∀ t₁ t₂, t₁ ≠ t₂ → Disjoint (layers t₁) (layers t₂)
  interval_property : ∀ S : Finset V, S.Nonempty →
    ({t : Fin k | ∃ F ∈ layers t, S ⊆ F} : Set (Fin k)).OrdConnected
