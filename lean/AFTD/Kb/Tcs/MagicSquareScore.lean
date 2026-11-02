import AFTD.Prelude

/-!
# magic_square_score

Topic: quantum   Node: 3160132ddcf4

Provenance: formalization of a published result. Source: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 6, proof of Theorem 6.1 (the winning effect W).

Given dA dB dE : ℕ, Alice's effects A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ (A x s: row x, then answer s), Bob's effects B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ (B j c: column j, then answer c), and a complex matrix ρ indexed by the product type (Fin dA × Fin dB) × Fin dE (the state on Alice, Bob and the adversary Eve, left-associated): magic_square_score A B ρ is the real number (1/9) · Σ_{x : Fin 3} Σ_{j : Fin 3} Σ_{s : Fin 3 → Bool} Σ_{c : Fin 3 → Bool} (if s j = c x then Re Tr(((A x s ⊗ₖ B j c) ⊗ₖ I_{Fin dE}) * ρ) else 0), with Kronecker products (Matrix.kronecker) grouped left as written and Re the real part of the complex trace. It is the score of the strategy: with row x and column j uniform and independent, the probability that Alice's j-th sign equals Bob's sign in row x, i.e. Tr(W ρ) with W = (1/9) Σ_{x,j,s,c} [s_j = c_x] A_{s|x} ⊗ B_{c|j} ⊗ I_E.
-/

/-- The winning probability of a magic-square strategy with uniform independent inputs: Alice gets row `x`, Bob column `j`, and they win when Alice's `j`-th sign equals Bob's sign in row `x`. -/
noncomputable def magic_square_score {dA dB dE : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ) : ℝ := open scoped Kronecker in
  (1 / 9 : ℝ) * ∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
    if s j = c x then
      (((A x s ⊗ₖ B j c) ⊗ₖ (1 : Matrix (Fin dE) (Fin dE) ℂ)) * ρ).trace.re
    else 0
