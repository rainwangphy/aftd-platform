import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPowerWellCoveredIffCliqueBlowup
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowup
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# forall_power_well_covered_iff_clique_blowup

Topic: graphs   Node: 58a76adb7cb9

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Theorem 1.6.

Let G be a finite simple graph and a_1, …, a_n positive integers, H = G[K_{a_1}, …, K_{a_n}] its clique blow-up. Then G^d is well-covered for all d ≥ 1 iff H^d is well-covered for all d ≥ 1.
-/

theorem forall_power_well_covered_iff_clique_blowup {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : V → ℕ) (ha : ∀ i, 0 < a i) :
    (∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) ↔
      (∀ d : ℕ, 1 ≤ d →
        simple_graph_is_well_covered (simple_graph_power (simple_graph_clique_blowup G a) d)) :=
  forall_congr' fun d => imp_congr_right fun hd =>
    simple_graph_power_well_covered_iff_clique_blowup G a ha d hd
