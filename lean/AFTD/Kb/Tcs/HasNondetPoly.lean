import AFTD.Prelude
import AFTD.Kb.Tcs.IsNondetPolynomial

/-!
# HasNondetPoly

Topic: circuits   Node: df7877feccf8

Provenance: formalization of a published result. Source: arXiv:2611.11966 Def 11

A Boolean function f : (Fin n → Bool) → Bool admits a non-deterministic polynomial of degree at most d if there exists a polynomial p : (Fin n → Bool) → ℝ satisfying IsNondetPolynomial f d p.
-/

/-- Predicate asserting that f has a non-deterministic polynomial of degree at most d. -/
def HasNondetPoly {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) : Prop := ∃ p : (Fin n → Bool) → ℝ, IsNondetPolynomial f d p
