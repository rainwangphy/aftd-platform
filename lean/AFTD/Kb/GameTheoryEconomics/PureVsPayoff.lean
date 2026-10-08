import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# pureVsPayoff

Topic: equilibria   Node: 0f877ece8acd

Provenance: formalization of a published result. Source: TCSlib, `pureVsPayoff`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a game $G$, a pure row $i$, and a mixed column strategy $q$, the
\emph{expected payoff of row $i$ against $q$} is
\[
  \mathrm{pureVsPayoff}(G, i, q) \;=\; \sum_{j} A_{ij} \cdot q_j.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The expected payoff to the row player when the row plays the pure action `i` and the column plays the mixed strategy `q`: the sum over columns `j` of `A(i, j) · q j` (in matrix form, `e_iᵀ A q`). [CBL06, §7.1]; [FS99, §2]. -/
noncomputable def pureVsPayoff {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) : ℝ :=
  ∑ j : Fin N, G.payoff i j * q.weights j
