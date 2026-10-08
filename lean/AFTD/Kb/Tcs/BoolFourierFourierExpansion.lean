import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierFourierCoeffEq
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion

/-!
# BoolFourier.fourier_expansion

Topic: interactive   Node: b8d093c83c10

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_expansion`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fourier–Walsh expansion. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function and let $x \in \{0,1\}^n$. Then $f$
agrees pointwise with the sum of its Walsh characters weighted by its Fourier
coefficients:
\[
  f(x) = \sum_{S \subseteq [n]} \hat f(S)\,\chi_S(x),
\]
where the sum ranges over all subsets $S$ of $[n]$, $\hat f(S) = \langle f,
\chi_S\rangle$ is the Fourier coefficient of $f$ at $S$, and $\chi_S$ is the Walsh
character of $S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Gives the Fourier--Walsh expansion of a Boolean-cube function. **Source:** [OD14, §1.3]. -/
lemma BoolFourier.fourier_expansion {n : ℕ} (f : BoolFun n) (x : hypercube n) :
    f x = ∑ S : Finset (Fin n), fourier_coeff f S * char_S S x := by
  simp_rw [fourier_coeff_eq]
  exact walsh_expansion f x

-- ∑_S f̂(S)² = ‖f‖₂²
