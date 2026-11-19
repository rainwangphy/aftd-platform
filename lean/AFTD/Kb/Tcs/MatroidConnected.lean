import AFTD.Prelude

/-!
# matroid_connected

Topic: algorithms   Node: 033cb648b7b4

Provenance: formalization of a published result. Source: arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier), Section 2 (connected matroid, in the equivalent form: any two distinct elements lie in a common circuit)

A matroid M on a type α is connected if for all elements e and f of its ground set M.E, either e = f or there is a circuit C of M that contains both e and f. (The matroid with empty ground set and every matroid with a one-element ground set are connected under this definition; for a nonempty ground set this is the usual notion: M is not a direct sum of two matroids with nonempty ground sets.)
-/

/-- A matroid is connected: any two distinct elements of its ground set lie in a common circuit. -/
def matroid_connected {α : Type*} (M : Matroid α) : Prop :=
  ∀ e ∈ M.E, ∀ f ∈ M.E, e = f ∨ ∃ C : Set α, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C
