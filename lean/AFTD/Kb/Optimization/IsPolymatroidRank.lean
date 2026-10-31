import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# is_polymatroid_rank

Topic: submodular   Node: b4eba624339b

Provenance: formalization of a published result. Source: arXiv:2610.35433:156; Edmonds 1970; Schrijver, Combinatorial Optimization, Section 44.1

A set function f on subsets of Fin n is a polymatroid rank function if it is normalized at the empty set (f ∅ = 0), nondecreasing with respect to inclusion, and submodular.
-/

/-- A polymatroid rank function is normalized at the empty set, monotone, and submodular. -/
def is_polymatroid_rank {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop := f ∅ = 0 ∧ Monotone f ∧ is_submodular f
