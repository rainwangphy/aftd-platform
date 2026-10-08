import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# bestColumn

Topic: equilibria   Node: 2e3e55032d41

Provenance: formalization of a published result. Source: TCSlib, `bestColumn`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a game $G$ and a mixed row strategy $p$, \texttt{bestColumn} is the pure
column $j^* \in \mathrm{Fin}\,N$ that minimises $\mathrm{payoffVsPure}(G, p,
\cdot)$, chosen via the classical axiom of choice from the finite minimiser.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A pure column best response to the row mixed strategy `p`: a column `j` minimizing the expected payoff `payoffVsPure G p j`. [FS99, §2 (best response)]. Finiteness lets us choose an actual minimizer, not just an infimum. -/
noncomputable def bestColumn {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) : Fin N :=
  Classical.choose (Finite.exists_min (payoffVsPure G p))
