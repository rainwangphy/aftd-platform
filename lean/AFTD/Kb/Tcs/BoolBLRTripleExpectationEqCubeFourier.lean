import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRTripleExpectationEqCubeFourierAuxHConvolution
import AFTD.Kb.Tcs.BoolBLRTripleExpectationEqCubeFourierAuxHSubstitute
import AFTD.Kb.Tcs.BoolFourierConvolution
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.triple_expectation_eq_cube_fourier

Topic: interactive   Node: 266e8201633d

Provenance: helper lemma. TCSlib, `BoolBLR.triple_expectation_eq_cube_fourier`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cube of Fourier coefficients as an autocorrelation expectation. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function on the hypercube, and let
$g = (-1)^{f}$ denote its $\pm 1$ lift. Then the double uniform expectation of the
triple product of $g$ over independent inputs and their componentwise XOR equals the sum
of the cubes of the Fourier coefficients of $g$:
\[
  \E_{x}\!\left[\,\E_{y}\!\left[\,g(x)\,g(y)\,g(x \oplus y)\,\right]\right]
  \;=\;
  \sum_{S \subseteq [n]} \hat{g}(S)^{3},
\]
where $x, y$ range uniformly over $\{0,1\}^n$, $(x \oplus y)_i = x_i \oplus y_i$, and
$\hat{g}(S) = \langle g, \chi_S \rangle$ is the Fourier coefficient at $S \subseteq
[n]$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Expresses the BLR triple correlation as the cube-sum of Fourier coefficients. **Source:** [OD14, §1.6 (Fourier soundness proof)]. -/
lemma BoolBLR.triple_expectation_eq_cube_fourier {n : ℕ} (f : hypercube n → Bool) :
  expectation (fun x =>
    expectation (fun y =>
      lift_pm1 f x * lift_pm1 f y * lift_pm1 f (xor_vec x y)))
  = ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 3 := by
  -- Step 1: Fourier expansion of f * f, with coefficients f̂(S)^2 by BoolFourier.convolution thm.
  -- Step 2: substitute into E[f(x)·(f*f)(x)] and pull the Fourier sum out.
  -- The final step: each E[f·χ_S] = f̂(S), so f̂(S)^2 · f̂(S) = f̂(S)^3.
  convert (triple_expectation_eq_cube_fourier_aux_h_substitute f (triple_expectation_eq_cube_fourier_aux_h_convolution f)) using 2;
  unfold BoolFourier.convolution; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  unfold expectation; norm_num [ Finset.mul_sum _ _ _ ] ;
  simp +decide only [Finset.sum_div, Finset.mul_sum _ _ _, mul_div]
  all_goals (rw [pow_succ]; rfl)

-- if f is epsilon-far from a given linear function (i.e., chi_S), then f-hat (S) ≤ 1 - 2 * ε
