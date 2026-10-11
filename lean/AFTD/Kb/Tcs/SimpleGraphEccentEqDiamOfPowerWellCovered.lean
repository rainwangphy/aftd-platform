import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPowerWellCoveredNotBallUnionSubset
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# simple_graph_eccent_eq_diam_of_power_well_covered

Topic: graphs   Node: 944a8bfef2f9

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Lemma 2.5, for D ≥ 2 (for D ≤ 1 the power G^{D−1} is edgeless); proof via Lemma 2.7 (simple_graph_power_well_covered_not_ball_union_subset) with w the vertex of small eccentricity.

Let G be a finite connected graph of diameter D ≥ 2 such that G^{D−1} is well-covered. Then every vertex of G has eccentricity D (G is self-centered).
-/

theorem simple_graph_eccent_eq_diam_of_power_well_covered {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hD : 2 ≤ G.diam)
    (hwc : simple_graph_is_well_covered (simple_graph_power G (G.diam - 1))) (v : V) :
    G.eccent v = G.diam := by
  have : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := (SimpleGraph.connected_iff_ediam_ne_top).1 hconn
  have hdiam : (G.diam : ℕ∞) = G.ediam := by
    rw [SimpleGraph.diam]; exact ENat.natCast_toNat htop
  apply le_antisymm (hdiam ▸ G.eccent_le_ediam)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨e, he⟩ : ∃ e : ℕ, G.eccent v = e := ⟨(G.eccent v).toNat,
    (ENat.natCast_toNat (ne_top_of_lt hlt)).symm⟩
  rw [he] at hlt
  norm_cast at hlt
  obtain ⟨s, t, hst⟩ := G.exists_edist_eq_ediam_of_finite
  refine simple_graph_power_well_covered_not_ball_union_subset G (G.diam - 1) (by omega) hwc s t v
    ?_ ?_
  · rw [hst, ← hdiam]; norm_cast; omega
  · intro x _
    calc G.edist v x ≤ G.eccent v := SimpleGraph.edist_le_eccent
      _ = e := he
      _ ≤ ((G.diam - 1 : ℕ) : ℕ∞) := by norm_cast; omega
