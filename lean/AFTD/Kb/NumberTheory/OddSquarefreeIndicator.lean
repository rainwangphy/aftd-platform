import AFTD.Prelude

/-!
# odd_squarefree_indicator

Topic: elementary_number_theory   Node: 9328bd136572

Provenance: formalization of a published result. Source: arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Definition 2.1

The integer-valued odd square-free indicator $\mu^*(d) \in \mathbb{Z}$, for a natural number $d$, is defined to be $1$ if for every prime natural number $p$ with $p \neq 2$, $p^2$ does not divide $d$, and $0$ otherwise.
-/

open Classical in
/-- The integer-valued odd square-free indicator μ*(d) ∈ ℤ, equal to 1 if p^2 ∤ d for all primes p ≠ 2, and 0 otherwise. -/
noncomputable def odd_squarefree_indicator (d : ℕ) : ℤ := if ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ d) then 1 else 0
