import AFTD.Prelude

/-!
# orderedFactorizationCount

Topic: combinatorics   Node: 37b748c34c6d

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Section 3 (H(m))

H(m), the number of ordered factorizations of m: the number of finite sequences of integers greater than 1 whose product is m, with H(1) = 1.
-/

/-- `H(m)`, the number of ordered factorizations of `m`: finite sequences of integers greater than one whose product is `m` (`H(1) = 1`, from the empty sequence). -/
noncomputable def orderedFactorizationCount (m : ℕ) : ℕ :=
  Nat.card {l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = m}
