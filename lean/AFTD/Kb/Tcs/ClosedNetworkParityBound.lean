import AFTD.Prelude

/-!
# closed_network_parity_bound

Topic: quantum   Node: 781a12c91c15

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 25

The parity bound for the closed network with n sources is 2^(1/2 - 1/(2n)).
-/

/-- The parity bound 2^(1/2 - 1/(2n)) for the closed network with n sources. -/
noncomputable def closed_network_parity_bound (n : ℕ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (n : ℝ)))
