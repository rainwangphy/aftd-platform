import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeCoil

/-!
# is_max_hypercube_coil

Topic: combinatorics   Node: 66630f18518b

Provenance: formalization of a published result. Source: arXiv:2610.36461 Section 2

A coil S in Q_n is a maximum coil if its cardinality is at least that of any other coil in Q_n.
-/

/-- A maximum coil in the hypercube Q_n is a coil of maximum cardinality. -/
def is_max_hypercube_coil (n : ℕ) (S : Finset (Fin n → Bool)) : Prop :=
  hypercube_coil n S ∧ ∀ S' : Finset (Fin n → Bool), hypercube_coil n S' → S'.card ≤ S.card
