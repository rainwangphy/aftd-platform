import AFTD.Prelude

/-!
# matrix_is_separable

Topic: quantum   Node: c2d2a524cab8

Provenance: formalization of a published result. Source: Standard definition of a separable (unentangled) bipartite positive operator, not normalised, as used in arXiv:quant-ph/0308032 (complete family of separability criteria), Section II; stated for OP-2299.

With dA dB : ℕ explicit arguments, in this order, and ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ, the proposition that ρ is separable (not necessarily normalised): there exist a natural number N and families of vectors x : Fin N → Fin dA → ℂ and y : Fin N → Fin dB → ℂ such that for all index pairs p, q : Fin dA × Fin dB the entry ρ p q equals the sum over i : Fin N of x i p.1 * star (x i q.1) * (y i p.2 * star (y i q.2)); that is, ρ = Σ_i |x_i⟩⟨x_i| ⊗ |y_i⟩⟨y_i| with unnormalised vectors (the weights are absorbed in the vectors).
-/

/-- A bipartite matrix is separable: a finite sum of tensor products of rank-one positive operators. -/
def matrix_is_separable (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  ∃ (N : ℕ) (x : Fin N → Fin dA → ℂ) (y : Fin N → Fin dB → ℂ),
    ∀ p q : Fin dA × Fin dB,
      ρ p q = ∑ i : Fin N, x i p.1 * star (x i q.1) * (y i p.2 * star (y i q.2))
