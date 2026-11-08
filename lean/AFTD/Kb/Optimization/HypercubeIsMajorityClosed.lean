import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeMaj

/-!
# hypercube_is_majority_closed

Topic: submodular   Node: 3b5482edf45a

Provenance: formalization of a published result. Source: arXiv:2610.38287 Section 2.3.1

A finite set X of Boolean vectors in Fin n → Bool is majority-closed (hypercube_is_majority_closed X) if for all x, y, z ∈ X, their componentwise majority hypercube_maj x y z belongs to X.
-/

/-- A set of vertices of the unit hypercube is majority-closed if it is closed under the componentwise majority operation. -/
def hypercube_is_majority_closed {n : ℕ} (X : Finset (Fin n → Bool)) : Prop := ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, hypercube_maj x y z ∈ X
