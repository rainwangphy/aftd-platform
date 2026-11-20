import AFTD.Prelude

/-!
# is_cap_set

Topic: combinatorics   Node: 0c1df07f3b01

Provenance: formalization of a published result. Source: arXiv:2611.20408, Section 1

A finite subset $C$ of $\mathbb{F}_3^n$ is a cap set if for every $x, y, z \in C$, $x + y + z = 0$ implies $x = y$ and $y = z$.
-/

/-- Predicate for a finite subset of $\mathbb{F}_3^n$ to be a cap set, having no three distinct elements summing to zero. -/
def is_cap_set (n : ℕ) (C : Finset (Fin n → ZMod 3)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → ∀ ⦃z⦄, z ∈ C → x + y + z = 0 → x = y ∧ y = z
