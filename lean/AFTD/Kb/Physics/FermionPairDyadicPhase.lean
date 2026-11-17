import AFTD.Prelude

/-!
# fermion_pair_dyadic_phase

Topic: quantum_mechanics   Node: 298d37529035

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

For natural numbers s and m, let A = (2 : ℝ)^s, p = 1 / (1 + A), wm = 2 * Nat.floor ((m : ℝ) * p / 2), and Cm = Nat.choose m wm. Then fermion_pair_dyadic_phase s m is defined as ((2 : ℝ) ^ (Nat.clog 2 Cm)) / (Cm : ℝ).
-/

/-- The dyadic phase parameter t_m in [1, 2] associated to the central even binomial coefficient. -/
noncomputable def fermion_pair_dyadic_phase (s : ℕ) (m : ℕ) : ℝ :=
  let A : ℝ := (2 : ℝ) ^ s
  let p : ℝ := 1 / (1 + A)
  let wm : ℕ := 2 * Nat.floor ((m : ℝ) * p / 2)
  let Cm : ℕ := Nat.choose m wm
  ((2 : ℝ) ^ (Nat.clog 2 Cm)) / (Cm : ℝ)
