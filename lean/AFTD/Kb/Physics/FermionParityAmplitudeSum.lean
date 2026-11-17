import AFTD.Prelude

/-!
# fermion_parity_amplitude_sum

Topic: quantum_mechanics   Node: 08c9450a6425

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

For natural numbers m, η, N and real numbers p, q, fermion_parity_amplitude_sum m p q η N is the sum over j in Finset.range (m + 1) of (taken : ℝ) * Real.sqrt (p^w * q^(m - w)), where w = η + 2 * j, cum = ∑ i in Finset.range j, Nat.choose m (η + 2 * i), and taken = min (Nat.choose m w) (N - cum).
-/

/-- Sum of the largest N Schmidt amplitudes in parity sector η for m pairs. -/
noncomputable def fermion_parity_amplitude_sum (m : ℕ) (p q : ℝ) (η : ℕ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    let w : ℕ := η + 2 * j
    let cum : ℕ := ∑ i ∈ Finset.range j, Nat.choose m (η + 2 * i)
    let taken : ℕ := min (Nat.choose m w) (N - cum)
    (taken : ℝ) * Real.sqrt (p ^ w * q ^ (m - w))
