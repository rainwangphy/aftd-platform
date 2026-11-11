import AFTD.Prelude
import AFTD.Kb.Tcs.DegreeSpace

/-!
# IsNondetPolynomial

Topic: circuits   Node: 3813a9e05fa6

Provenance: formalization of a published result. Source: arXiv:2611.11966 Def 11

A real-valued function p on the Boolean hypercube (Fin n → Bool) is a non-deterministic polynomial for a Boolean function f of degree at most d if p belongs to degreeSpace ℝ (Fin n) d and for all x : Fin n → Bool, p x ≠ 0 if and only if f x = true.
-/

/-- A real function p is a non-deterministic polynomial for f of degree at most d. -/
def IsNondetPolynomial {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (p : (Fin n → Bool) → ℝ) : Prop := p ∈ degreeSpace ℝ (Fin n) d ∧ ∀ x, p x ≠ 0 ↔ f x = true
