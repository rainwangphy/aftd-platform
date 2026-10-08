import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# payoffVsPure

Topic: equilibria   Node: de0a8d4be6e3

Provenance: formalization of a published result. Source: TCSlib, `payoffVsPure`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a game $G$, a mixed row strategy $p$, and a pure column $j$, the
\emph{expected payoff against column $j$} is
\[
  \mathrm{payoffVsPure}(G, p, j) \;=\; \sum_{i} p_i \cdot A_{ij}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The expected payoff to the row player when the row plays the mixed strategy `p` and the column plays the pure action `j`: the sum over rows `i` of `p i · A(i, j)` (in matrix form, `pᵀ A e_j`). [CBL06, §7.1]; [FS99, §2]. -/
noncomputable def payoffVsPure {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) : ℝ :=
  ∑ i : Fin M, p.weights i * G.payoff i j
