import AFTD.Prelude

/-!
# magic_square_winning_op

Topic: quantum   Node: e845868b8d8a

Provenance: formalization of a published result. Source: arXiv:2610.12001, page 19, line 1027

Given dimensions dA and dB, Alice's matrix effects A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ and Bob's matrix effects B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ, the bipartite winning operator is the (dA × dB) by (dA × dB) complex matrix given by (1 / 9 : ℂ) • ∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool, if s j = c x then (A x s ⊗ₖ B j c) else 0, where ⊗ₖ is the matrix Kronecker product.
-/

/-- The bipartite winning operator for the magic square game with Alice's effects A and Bob's effects B. -/
noncomputable def magic_square_winning_op {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := open scoped Kronecker in
  (1 / 9 : ℂ) • ∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
    if s j = c x then (A x s ⊗ₖ B j c) else 0
