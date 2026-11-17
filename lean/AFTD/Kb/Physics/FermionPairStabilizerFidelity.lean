import AFTD.Prelude
import AFTD.Kb.Physics.FermionParityAmplitudeSum

/-!
# fermion_pair_stabilizer_fidelity

Topic: quantum_mechanics   Node: c30275344918

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

The function fermion_pair_stabilizer_fidelity (s m : ℕ) : ℝ returns the real number given by the maximum of (Finset.range m).fold max 0 (fun k => max (pure_val k 0) (pure_val k 1)) and (Finset.Icc 1 m).fold max 0 bal_val, evaluating to 0 when m = 0, where A = (2 : ℝ)^s, p = 1 / (1 + A), q = 1 - p, pure_val k η = (2 : ℝ)^(-(k : ℤ)) * (fermion_parity_amplitude_sum m p q η (2^k))^2, and bal_val k = (2 : ℝ)^(-(k : ℤ)) * (fermion_parity_amplitude_sum m p q 0 (2^(k-1)) + fermion_parity_amplitude_sum m p q 1 (2^(k-1)))^2.
-/

/-- The maximum parity-preserving local-unitary stabilizer fidelity F_m of m identical fermion pairs. -/
noncomputable def fermion_pair_stabilizer_fidelity (s : ℕ) (m : ℕ) : ℝ :=
  let A : ℝ := (2 : ℝ) ^ s
  let p : ℝ := 1 / (1 + A)
  let q : ℝ := 1 - p
  let pure_val (k : ℕ) (η : ℕ) : ℝ :=
    (2 : ℝ) ^ (- (k : ℤ)) * (fermion_parity_amplitude_sum m p q η (2 ^ k)) ^ 2
  let bal_val (k : ℕ) : ℝ :=
    (2 : ℝ) ^ (- (k : ℤ)) * (fermion_parity_amplitude_sum m p q 0 (2 ^ (k - 1)) +
      fermion_parity_amplitude_sum m p q 1 (2 ^ (k - 1))) ^ 2
  max ((Finset.range m).fold max 0 (fun k => max (pure_val k 0) (pure_val k 1)))
      ((Finset.Icc 1 m).fold max 0 bal_val)
