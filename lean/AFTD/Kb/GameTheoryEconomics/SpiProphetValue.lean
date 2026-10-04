import AFTD.Prelude

/-!
# spi_prophet_value

Topic: mechanism_design   Node: 718bf673afd6

The prophet benchmark OPT = E[max_i X_i] for independent finite-support rewards.
-/

open Finset in
/-- The prophet benchmark `OPT = E[max_i X_i]` for independent finite-support rewards. -/
noncomputable def spi_prophet_value {N K : ℕ} (x w : Fin (N + 1) → Fin K → ℝ) : ℝ :=
  ∑ k : Fin (N + 1) → Fin K, (∏ i, w i (k i)) * univ.sup' univ_nonempty (fun i => x i (k i))
