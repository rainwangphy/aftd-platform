import AFTD.Prelude

/-!
# nonzero_roots_eq_of_charpoly_eq_X_pow

Topic: quantum   Node: 0db4d910c1fb

Provenance: formalization of a published result. Source: QuantumInfo, `nonzero_roots_eq_of_charpoly_eq_X_pow`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two polynomials differ by a factor of X^k, their non-zero roots are the same.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace in
/-- If two polynomials differ by a factor of X^k, their non-zero roots are the same. -/
lemma nonzero_roots_eq_of_charpoly_eq_X_pow {R : Type*} [CommRing R] [IsDomain R]
  [DecidableEq R] (p q : Polynomial R) (k : ℕ) (h : p = Polynomial.X ^ k * q) :
    p.roots.filter (· ≠ 0) = q.roots.filter (· ≠ 0) := by
  by_cases hq : q = 0 <;> simp_all [ Polynomial.roots_mul, Polynomial.X_ne_zero ]
