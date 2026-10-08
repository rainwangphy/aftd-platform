import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteLowerValue
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteLowerValueBddAbove
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteLowerValueLeUpperValue
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperValue
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperValueBddBelow
import AFTD.Kb.GameTheoryEconomics.OnlineLearningPureVsPayoffLeOne
import AFTD.Kb.GameTheoryEconomics.ApproxMinimax
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMixedStrategyNonempty

/-!
# OnlineLearning.finite_minimax_value

Topic: equilibria   Node: 127ed51ae9b1

Provenance: formalization of a published result. Source: Minimax theorem for finite zero-sum games, as formalized in TCSlib (`OnlineLearning.finite_minimax_value`). Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Minimax theorem for finite zero-sum games. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, whose payoff matrix $A = (A_{ij})$ satisfies $0 \le A_{ij} \le 1$ for all
$i,j$. Suppose $M > 1$ and $N \ge 1$. Then the lower and upper values of $G$ coincide:
\[
  \sup_{p \in \Delta_M}\; \inf_{j \in [N]}\; \sum_{i} p_i\, A_{ij}
  \;=\;
  \inf_{q \in \Delta_N}\; \sup_{i \in [M]}\; \sum_{j} A_{ij}\, q_j,
\]
where $\Delta_M$ and $\Delta_N$ denote the sets of mixed strategies (probability
distributions) over the row and column actions respectively.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The minimax theorem for finite zero-sum games (von Neumann): for a game `G` with at least two row actions, the lower value `sup_p inf_j payoff(p, j)` equals the upper value `inf_q sup_i payoff(i, q)`. [CBL06, Thm 7.1 (finite case)]; [FS99, §5 (proof of the minmax theorem), §6.1]. Deviation: the proof goes through the Hedge-based `approx_minimax`, so it carries the spurious hypothesis `1 < M` (at least two row actions), which the theorem itself does not need; the case `M = 1` is not covered here. **Proof sketch.** By `le_antisymm`. Step 1 (easy direction): the lower value is at most the upper value by `finiteLowerValue_le_upperValue` (weak duality). Step 2 (hard direction): it suffices to show `upper ≤ lower + ε` for every `ε > 0`. Fix `ε`; the ε-approximate saddle point `(p, q)` from `approx_minimax` gives (`hq_le`) `sup_i payoff(i, q) ≤ inf_j payoff(p, j) + ε`. Then `upper ≤ sup_i payoff(i, q)` since the upper value is an infimum over `q` (`h_upper_at_q`), and `inf_j payoff(p, j) ≤ lower` since the lower value is a supremum over `p` (`h_lower_at_p`); chain the three inequalities. -/
theorem OnlineLearning.finite_minimax_value {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (hM : 1 < M) :
    finiteLowerValue G = finiteUpperValue G := by
  apply le_antisymm
  -- Step 1: the easy direction is weak duality.
  · exact finiteLowerValue_le_upperValue G
  -- Step 2: the hard direction by ε-approximation.
  · apply le_of_forall_pos_le_add
    intro ε hε
    -- The approximate minimax theorem gives strategies whose gap is at most
    -- `ε`.  Since this works for every positive `ε`, the exact values are equal.
    obtain ⟨p, q, hpq⟩ := approx_minimax G hM ε hε
    -- `hq_le`: the saddle-point gap bounds the row supremum by the column infimum.
    have hq_le :
        (⨆ i : Fin M, pureVsPayoff G i q) ≤
          (⨅ j : Fin N, payoffVsPure G p j) + ε := by
      have hbdd : BddAbove (Set.range (fun i : Fin M => pureVsPayoff G i q)) :=
        ⟨1, by rintro _ ⟨i, rfl⟩; exact pureVsPayoff_le_one G i q⟩
      apply ciSup_le
      intro i
      have hle_inf :
          pureVsPayoff G i q - ε ≤ ⨅ j : Fin N, payoffVsPure G p j := by
        apply le_ciInf
        intro j
        linarith [hpq i j]
      linarith
    -- `h_upper_at_q`: the upper value is at most its value at `q`.
    have h_upper_at_q :
        finiteUpperValue G ≤ ⨆ i : Fin M, pureVsPayoff G i q := by
      unfold finiteUpperValue
      exact ciInf_le (finiteUpperValue_bddBelow G) q
    -- `h_lower_at_p`: the lower value is at least its value at `p`.
    have h_lower_at_p :
        (⨅ j : Fin N, payoffVsPure G p j) ≤ finiteLowerValue G := by
      unfold finiteLowerValue
      exact le_ciSup (finiteLowerValue_bddAbove G) p
    linarith
