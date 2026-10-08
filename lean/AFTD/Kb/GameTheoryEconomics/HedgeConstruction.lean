import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HedgeResponseNatIsBestResponse
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.Tcs.HedgeRegretBoundTight
import AFTD.Kb.GameTheoryEconomics.HedgeResponseNat
import AFTD.Kb.Tcs.CumLossHorizon
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.GameTheoryEconomics.PayoffVsPureAverageStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.AverageStrategy
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeCumLoss
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.Regret
import AFTD.Kb.GameTheoryEconomics.EmpiricalStrategy
import AFTD.Kb.Tcs.HedgeDistNonneg
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeqValid
import AFTD.Kb.GameTheoryEconomics.RegretToPayoff
import AFTD.Kb.Tcs.BestExpertLoss
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure
import AFTD.Kb.GameTheoryEconomics.PureVsPayoffEmpiricalStrategy
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeDistSum
import AFTD.Kb.Tcs.CumLoss

/-!
# hedge_construction

Topic: equilibria   Node: 7d53355dd517

Provenance: helper lemma. TCSlib, `hedge_construction`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/FiniteMinimax.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Hedge yields an approximate minimax pair. Let $G$ be a finite two-player zero-sum game with $M \ge 2$ row actions and $N \ge 1$
column actions, with payoff matrix $(A_{ij})$ satisfying $0 \le A_{ij} \le 1$; the row
player maximises and the column player minimises. Fix an integer $T > 0$ and a learning
rate $\eta > 0$. Then there exist a mixed row strategy $p$ and a mixed column strategy
$q$ such that, for every pure row $i \in \{1,\dots,M\}$ and every pure column $j \in
\{1,\dots,N\}$,
\[
  \sum_{i'} p_{i'}\,A_{i'j} \;+\; \frac{(\ln M)/\eta + \eta T/8}{T}
  \;\ge\;
  \sum_{j'} A_{ij'}\,q_{j'}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The Hedge construction: given a game `G` with `M ≥ 2` rows, a horizon `T > 0`, and a learning rate `η > 0`, there exist mixed strategies `p`, `q` such that for all pure `i`, `j`, `payoffVsPure G p j + (log M / η + η T / 8) / T ≥ pureVsPayoff G i q`. Here `p` is the time average of the Hedge distributions played on the losses `1 − A(·, j_t)` and `q` is the empirical distribution of the columns `j_t`, each of which is a pure best response to the current Hedge distribution. [FS99, §§5–6.1]; [CBL06, proof of Thm 7.1]. The hypothesis `1 < M` is not used by this lemma's proof (it is carried for `approx_minimax`). **Proof sketch.** Step 1 (`hvalid`): generate the online column responses `hedgeResponseNat`, form the induced loss sequence `ℓ` (valid, since payoffs lie in `[0, 1]`), and record the Hedge distributions `strategies t := hedgeDist η ℓ t`; take `p := averageStrategy` and `q := empiricalStrategy`. Step 2 (`hreg`): the tight Hedge regret bound `log M / η + η T / 8` on `ℓ` (`hedge_regret_bound_tight`), read through `regret_to_payoff`, says the realized payoff sum is at least the best fixed row's payoff sum minus `R`. Step 3 (`hbest_sum`): by `hedgeResponseNat_isBestResponse`, replacing each played column by the fixed column `j` can only increase the row payoff, round by round. Step 4 (`hmain`): for the fixed row `i`, chain Steps 2 and 3 (`i`'s payoff sum is at most the supremum) and divide by `T`. Step 5 (`hpj`, `hqi`): both sides of the goal are the time averages computed in `payoffVsPure_averageStrategy` and `pureVsPayoff_empiricalStrategy`; conclude by linear arithmetic. -/
lemma hedge_construction {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (_hM : 1 < M)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη_pos : 0 < η) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + (Real.log M / η + η * T / 8) / T ≥
          pureVsPayoff G i q := by
  classical
  -- Step 1 (`hvalid`): generate the online column responses, turn them into a
  -- valid Hedge loss sequence, and record the row distributions Hedge plays.
  let actions : Fin T → Fin N := fun t => hedgeResponseNat G η t.val
  let ℓ : LossSeq M T := G.toLossSeq actions
  let strategies : Fin T → Fin M → ℝ := fun t i => hedgeDist η ℓ t.val i
  have h_nonneg : ∀ t i, 0 ≤ strategies t i := fun t i => hedgeDist_nonneg η ℓ t.val i
  have h_sum : ∀ t, ∑ i : Fin M, strategies t i = 1 := fun t => hedgeDist_sum η ℓ t.val
  have hvalid : ℓ.Valid := ZeroSumGame.toLossSeq_valid G actions
  refine ⟨averageStrategy hT strategies h_nonneg h_sum, empiricalStrategy hT actions, ?_⟩
  intro i j
  set R : ℝ := Real.log ↑M / η + η * ↑T / 8 with hR
  -- Step 2 (`hreg`): the tight Hedge bound on `ℓ`, translated into a payoff
  -- guarantee against the best fixed row action (`regret_to_payoff`).
  have hreg :
      ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≥
        ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (actions t) - R := by
    have hbestEq :
        bestExpertLoss ℓ =
          ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (actions t))) := by
      unfold bestExpertLoss
      congr 1
      ext i
      rw [cumLoss_horizon]
      rfl
    have hreg' :
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * (1 - G.payoff i (actions t))) -
          ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (actions t))) ≤ R := by
      simpa only [R, regret, hedgeCumLoss, hedgeLoss, strategies, ℓ, ZeroSumGame.toLossSeq,
        hbestEq] using hedge_regret_bound_tight η hη_pos ℓ hvalid
    exact regret_to_payoff G hT strategies h_sum actions R hreg'
  -- Step 3 (`hbest_sum`): each generated column is a best response to the
  -- current Hedge distribution, so replacing it by the fixed column `j` can
  -- only increase the row payoff, round by round.
  have hbest_sum :
      ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j :=
    Finset.sum_le_sum fun t _ => hedgeResponseNat_isBestResponse G η t j
  -- Step 4 (`hmain`): combine Steps 2 and 3 for the fixed row `i`, then divide
  -- by `T`.
  have hmain :
      (∑ t : Fin T, G.payoff i (actions t)) / ↑T - R / ↑T ≤
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
    have hi_sup : (∑ t : Fin T, G.payoff i (actions t)) - R ≤
        ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (actions t) - R := by
      have hbdd : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (actions t) - R)) :=
        Set.Finite.bddAbove (Set.finite_range _)
      exact le_ciSup hbdd i
    have hTpos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
    have := div_le_div_of_nonneg_right (show ∑ t : Fin T, G.payoff i (actions t) - R ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j by linarith) hTpos.le
    field_simp at this ⊢
    linarith
  -- Step 5 (`hpj`, `hqi`): both sides of the goal are time averages.
  have hpj :
      payoffVsPure G (averageStrategy hT strategies h_nonneg h_sum) j =
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T :=
    payoffVsPure_averageStrategy G hT strategies h_nonneg h_sum j
  have hqi :
      pureVsPayoff G i (empiricalStrategy hT actions) =
        (∑ t : Fin T, G.payoff i (actions t)) / ↑T :=
    pureVsPayoff_empiricalStrategy G hT actions i
  rw [hpj, hqi, hR]
  linarith
