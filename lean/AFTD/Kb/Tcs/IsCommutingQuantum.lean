import AFTD.Prelude

/-!
# is_commuting_quantum

Topic: communication   Node: fb5ddd18b509

Provenance: formalization of a published result. Source: arXiv:2610.41448, An Unbounded Separation of Almost-Quantum and Commuting-Operator Correlations in Zero-Error Communication, Sec. 2

A bipartite behaviour p : X → Y → A → B → ℝ belongs to the commuting-operator quantum set C_qc if there exist a real Hilbert space E, a unit state vector ψ ∈ E, and projective measurements A_meas : X → A → (E →L[ℝ] E) and B_meas : Y → B → (E →L[ℝ] E) such that Alice and Bob's measurement operators commute as operators on E and the joint probabilities equal the quantum expectation values p(x, y, a, b) = ⟪ψ, A_meas(x, a) B_meas(y, b) ψ⟫.
-/

/-- A bipartite correlation belongs to the commuting-operator quantum set C_qc if it is realized by commuting projective measurements on a Hilbert space. -/
def is_commuting_quantum {X Y A B : Type*} [Fintype A] [Fintype B]
    (p : X → Y → A → B → ℝ) : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
    (ψ : E) (_ : ‖ψ‖ = 1)
    (A_meas : X → A → (E →L[ℝ] E))
    (_ : ∀ x, (∀ a, IsStarProjection (A_meas x a)) ∧ ∑ a, A_meas x a = 1)
    (B_meas : Y → B → (E →L[ℝ] E))
    (_ : ∀ y, (∀ b, IsStarProjection (B_meas y b)) ∧ ∑ b, B_meas y b = 1),
    (∀ x y a b v, (A_meas x a) ((B_meas y b) v) = (B_meas y b) ((A_meas x a) v)) ∧
    ∀ x y a b, p x y a b = inner ℝ ψ ((A_meas x a) ((B_meas y b) ψ))
