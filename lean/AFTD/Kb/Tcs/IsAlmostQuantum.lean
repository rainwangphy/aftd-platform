import AFTD.Prelude

/-!
# is_almost_quantum

Topic: quantum   Node: 423987ecc0d6

Provenance: formalization of a published result. Source: arXiv:2610.41448 Definition 1

A bipartite behaviour p belongs to the almost-quantum set C_AQ if there exist a real Hilbert space E, a unit state vector ψ, and projective measurements A for Alice and B for Bob such that Alice and Bob's measurement operators commute on ψ and the joint probabilities equal the quantum expectation values ⟪ψ, A_{a|x} B_{b|y} ψ⟫.
-/

/-- A bipartite behaviour belongs to the almost-quantum set C_AQ if it can be realized by projective measurements commuting on a shared state vector. -/
def is_almost_quantum {X Y A B : Type*} [Fintype A] [Fintype B]
    (p : X → Y → A → B → ℝ) : Prop := ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
    (ψ : E) (_ : ‖ψ‖ = 1)
    (A_meas : X → A → E →L[ℝ] E) (_ : ∀ x, (∀ a, IsStarProjection (A_meas x a)) ∧ (∑ a, A_meas x a = 1))
    (B_meas : Y → B → E →L[ℝ] E) (_ : ∀ y, (∀ b, IsStarProjection (B_meas y b)) ∧ (∑ b, B_meas y b = 1)),
    (∀ x y a b, A_meas x a (B_meas y b ψ) = B_meas y b (A_meas x a ψ)) ∧
    (∀ x y a b, p x y a b = inner ℝ ψ (A_meas x a (B_meas y b ψ)))
