import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleTransportPlanMainMarginals
import AFTD.Kb.Tcs.GraphIdleTransportPlanMainCost
import AFTD.Kb.Tcs.GraphMinDegreeEdgePartitionBCardLe
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOne
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOneBoundary
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOneOfBEqZero
import AFTD.Kb.Tcs.GraphEdgePartitionSpecialStructure
import AFTD.Kb.Tcs.GraphIdleTransportPlanSpecial
import AFTD.Kb.Tcs.GraphIdleSpecialCostLtOne
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDistComm
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleTransportPlanMain
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_wasserstein_lt_one_of_edge_partition

Topic: graphs   Node: ec919eb8711d

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

Given the edge partition of a graph of diameter at most 2 whose minimum degree is at least 2n/3 − 1, the idleness-1/2 measures at the endpoints of the edge are at Wasserstein distance less than 1.
-/

lemma graph_idle_wasserstein_lt_one_of_edge_partition_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (hdiam : G.ediam ≤ 2)
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ))
    (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hn : Fintype.card V = 2 + A.card + B.card + C.card + P.card)
    (hle : G.degree x ≤ G.degree y) :
    graph_wasserstein_dist G (graph_idle_measure G (1/2) x) (graph_idle_measure G (1/2) y) < 1 := by
  have hpos_dx : 1 ≤ G.degree x := by omega
  have hab : A.card ≤ B.card := by omega
  have hb_le : B.card ≤ C.card + 2 :=
    graph_min_degree_edge_partition_b_card_le G hδ x y A B C P hdx hdy hn
  rcases eq_or_lt_of_le hb_le with hb_eq | hb_lt
  · -- Case B.card = C.card + 2
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- Subcase G.degree x = G.degree y
      have hspec := graph_edge_partition_special_structure G hδ x y A B C P
        hAmem hBmem hCmem hPmem hcover hdx hdy hn heq hb_eq
      rcases hspec with ⟨-, hAB, hadj⟩
      have hne : 1 ≤ A.card := by omega
      obtain ⟨π, hπ_nonneg, hπ_row, hπ_col, hπ_cost⟩ :=
        graph_idle_transport_plan_special G x y hxy hdiam A B C P
          hAmem hBmem hCmem hPmem hcover hdx hdy hAB hne hadj
      have hdist_le := graph_wasserstein_dist_le_of_plan G
        (graph_idle_measure G (1/2) x) (graph_idle_measure G (1/2) y) π hπ_nonneg hπ_row hπ_col
      have hcost_lt := graph_idle_special_cost_lt_one A.card B.card C.card (G.degree y) hAB hb_eq hdy
      exact lt_of_le_of_lt (hdist_le.trans hπ_cost) hcost_lt
    · -- Subcase G.degree x < G.degree y
      obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ :=
        graph_idle_transport_plan_main_marginals G x y hxy A B C P
          hAmem hBmem hCmem hPmem hcover hdx hdy hle hab
      have hcost_le := graph_idle_transport_plan_main_cost G x y hxy hdiam A B C P
        hAmem hBmem hCmem hPmem hcover hdx hdy hle
      have hdist_le := graph_wasserstein_dist_le_of_plan G
        (graph_idle_measure G (1/2) x) (graph_idle_measure G (1/2) y)
        (graph_idle_transport_plan_main G x y A B C) hπ_nonneg hπ_row hπ_col
      have hcost_lt := graph_idle_plan_cost_lt_one_boundary
        (G.degree x) (G.degree y) A.card B.card C.card hpos_dx hlt hdx hdy hb_eq
      exact lt_of_le_of_lt (hdist_le.trans hcost_le) hcost_lt
  · -- Case B.card ≤ C.card + 1
    have hb_le' : B.card ≤ C.card + 1 := by omega
    obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ :=
      graph_idle_transport_plan_main_marginals G x y hxy A B C P
        hAmem hBmem hCmem hPmem hcover hdx hdy hle hab
    have hcost_le := graph_idle_transport_plan_main_cost G x y hxy hdiam A B C P
      hAmem hBmem hCmem hPmem hcover hdx hdy hle
    have hdist_le := graph_wasserstein_dist_le_of_plan G
      (graph_idle_measure G (1/2) x) (graph_idle_measure G (1/2) y)
      (graph_idle_transport_plan_main G x y A B C) hπ_nonneg hπ_row hπ_col
    have hcost_lt := graph_idle_plan_cost_lt_one
      (G.degree x) (G.degree y) A.card B.card C.card hpos_dx hle hdx hdy hb_le'
    exact lt_of_le_of_lt (hdist_le.trans hcost_le) hcost_lt

/-- Assembly: for an edge partition of a diameter-2 graph with min degree at least 2n/3 - 1, W(μ_x^{1/2}, μ_y^{1/2}) < 1. -/
theorem graph_idle_wasserstein_lt_one_of_edge_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (hdiam : G.ediam ≤ 2)
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ))
    (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hn : Fintype.card V = 2 + A.card + B.card + C.card + P.card) :
    graph_wasserstein_dist G (graph_idle_measure G (1/2) x) (graph_idle_measure G (1/2) y) < 1 := by
  rcases le_total (G.degree x) (G.degree y) with hle | hle
  · exact graph_idle_wasserstein_lt_one_of_edge_partition_aux G x y hxy hdiam hδ
      A B C P hAmem hBmem hCmem hPmem hcover hdx hdy hn hle
  · rw [graph_wasserstein_dist_comm]
    have hcover_swap : (Finset.univ : Finset V) = {y} ∪ {x} ∪ B ∪ A ∪ C ∪ P := by
      rw [hcover]
      ext v
      simp only [Finset.mem_union, Finset.mem_singleton]
      tauto
    have hCmem_swap : ∀ v, v ∈ C ↔ (G.Adj y v ∧ G.Adj x v) := by
      intro v
      rw [hCmem, and_comm]
    have hPmem_swap : ∀ v, v ∈ P ↔ (¬ G.Adj y v ∧ ¬ G.Adj x v) := by
      intro v
      rw [hPmem, and_comm]
    have hn_swap : Fintype.card V = 2 + B.card + A.card + C.card + P.card := by
      omega
    exact graph_idle_wasserstein_lt_one_of_edge_partition_aux G y x hxy.symm hdiam hδ
      B A C P hBmem hAmem hCmem_swap hPmem_swap hcover_swap hdy hdx hn_swap hle
