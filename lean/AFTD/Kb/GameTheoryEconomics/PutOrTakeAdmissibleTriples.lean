import AFTD.Prelude

/-!
# PutOrTakeAdmissibleTriples

Topic: combinatorial_games   Node: b0e04a0c8bcd

Provenance: formalization of a published result. Source: arXiv:2611.05898 -- An Asymptotic for E. P. Stein Numbers

The set $\mathcal{A}$ of triples $(d, u, v)$ of positive integers such that $u$ is odd, $p^2 \nmid d$ for all odd primes $p$, and $d(u^2 - 2v^2)^2 \le 4uv$.
-/

/-- The set of triples (d, u, v) of positive integers with u odd, d having no odd square prime factors, and d(u^2 - 2v^2)^2 ≤ 4uv. -/
def PutOrTakeAdmissibleTriples : Set (ℕ × ℕ × ℕ) := {t : ℕ × ℕ × ℕ |
  0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
  Odd t.2.1 ∧
  (∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p^2 ∣ t.1)) ∧
  (t.1 : ℤ) * ((t.2.1 : ℤ)^2 - 2 * (t.2.2 : ℤ)^2)^2 ≤ 4 * (t.2.1 : ℤ) * (t.2.2 : ℤ)}
