import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEccentEqDiamOfPowerWellCovered
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# simple_graph_no_leaf_of_power_well_covered

Topic: graphs   Node: 9a4efa2c51c2

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Corollary 2.6.

Let G be a finite connected graph of diameter D ≥ 2 such that G^{D−1} is well-covered. Then G has no leaves (no vertex of degree 1).
-/

theorem simple_graph_no_leaf_of_power_well_covered {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hD : 2 ≤ G.diam)
    (hwc : simple_graph_is_well_covered (simple_graph_power G (G.diam - 1))) (v : V) :
    G.degree v ≠ 1 := by
  intro hdeg
  obtain ⟨u, hvu, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1 hdeg
  have : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := (SimpleGraph.connected_iff_ediam_ne_top).1 hconn
  have hdiam : (G.diam : ℕ∞) = G.ediam := by
    rw [SimpleGraph.diam]; exact ENat.natCast_toNat htop
  have hecc := simple_graph_eccent_eq_diam_of_power_well_covered G hconn hD hwc u
  have hle : G.eccent u ≤ ((G.diam - 1 : ℕ) : ℕ∞) := by
    rw [SimpleGraph.eccent_le_iff]
    intro w
    by_cases hwv : w = v
    · subst hwv
      rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_one_iff_adj.2 hvu]
      norm_cast; omega
    · obtain ⟨p, hp⟩ := (hconn v w).exists_walk_length_eq_edist
      cases p with
      | nil => exact absurd rfl hwv
      | cons h p' =>
        rename_i x
        have hx : x = u := huniq x h
        subst hx
        have h1 : G.edist x w ≤ p'.length := SimpleGraph.edist_le p'
        have h2 : G.edist v w ≤ G.diam := by rw [hdiam]; exact SimpleGraph.edist_le_ediam
        rw [← hp, SimpleGraph.Walk.length_cons] at h2
        have h3 : p'.length + 1 ≤ G.diam := by exact_mod_cast h2
        calc G.edist x w ≤ p'.length := h1
          _ ≤ ((G.diam - 1 : ℕ) : ℕ∞) := by norm_cast; omega
  rw [hecc] at hle
  norm_cast at hle
  omega
