import AFTD.Prelude

/-!
# random_ising_magic_expected

Topic: quantum_mechanics   Node: 371b93d594c1

Provenance: formalization of a published result. Source: arXiv:2610.27080, Rényi multi-entropy of graph states and the n -> 1 limit

For a natural number n, random_ising_magic_expected n is defined as 16 - 32 * (3 / 4)^n + 24 * (1 / 2)^n - 8 * (1 / 4)^n as a real number.
-/

/-- Expected normalized magic 16 - 32*(3/4)^n + 24*(1/2)^n - 8*(1/4)^n of G(n, 1/2) Ising graph states. -/
noncomputable def random_ising_magic_expected (n : ℕ) : ℝ := 16 - 32 * (3 / 4 : ℝ) ^ n + 24 * (1 / 2 : ℝ) ^ n - 8 * (1 / 4 : ℝ) ^ n
