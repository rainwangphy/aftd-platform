import AFTD.Prelude

/-!
# von_neumann_entropy

Topic: quantum_mechanics   Node: caf19579c335

Provenance: formalization of a published result. Source: von Neumann 1927; Nielsen & Chuang, Section 11.3

For an n-by-n complex matrix ρ indexed by a finite type n with decidable equality, von_neumann_entropy ρ is the real number defined as the sum over all i : n of Real.negMulLog (h.eigenvalues i) if ρ is Hermitian with proof h, and 0 otherwise.
-/

/-- Von Neumann entropy of a complex matrix in nats, defined via real eigenvalues when Hermitian and 0 otherwise. -/
noncomputable def von_neumann_entropy {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ := if h : ρ.IsHermitian then ∑ i : n, Real.negMulLog (h.eigenvalues i) else 0
