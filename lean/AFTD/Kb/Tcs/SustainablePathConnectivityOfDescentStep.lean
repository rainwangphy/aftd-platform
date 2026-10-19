import AFTD.Prelude
import AFTD.Kb.Tcs.RelationReachesTerminalOfNatRankDescent
import AFTD.Kb.Tcs.CardFilterLtCardFilterOfLt
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.SustainableGtsStep
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsGeneralizedTreeShift

/-!
# sustainable_path_connectivity_of_descent_step

Topic: graphs   Node: d0702320baa1

Provenance: helper lemma. step towards op223_poset_connectivity

If every sustainable tree on Fin n (n ≥ 1) that is not a path has a sustainable generalized-tree-shift predecessor with strictly smaller adjacency spectral radius, then every sustainable tree on Fin n is reachable from some graph isomorphic to pathGraph n by a sequence of sustainable generalized tree shifts. This is the first conjunct of op223_poset_connectivity with the one-step descent claim isolated as a hypothesis.
-/

/-- The sustainable half of op223_poset_connectivity follows from the one-step descent claim plus finite descent on the spectral rank #{W | λ W < λ Z}. -/
theorem sustainable_path_connectivity_of_descent_step
    (hstep : ∀ (n : ℕ) (_hn : 1 ≤ n) (X : SimpleGraph (Fin n)), is_sustainable_tree X →
      ¬ Nonempty (X ≃g SimpleGraph.pathGraph n) →
      ∃ Y : SimpleGraph (Fin n), is_sustainable_tree Y ∧ is_generalized_tree_shift Y X ∧
        adjacency_spectral_radius Y < adjacency_spectral_radius X) :
    ∀ (n : ℕ) (_hn : 1 ≤ n) (X : SimpleGraph (Fin n)), is_sustainable_tree X →
      ∃ P : SimpleGraph (Fin n), Nonempty (P ≃g SimpleGraph.pathGraph n) ∧
        Relation.ReflTransGen sustainable_gts_step P X := by
  intro n hn X hX
  classical
  refine relation_reaches_terminal_of_nat_rank_descent
    (fun Z : SimpleGraph (Fin n) => is_sustainable_tree Z)
    (fun Z : SimpleGraph (Fin n) => Nonempty (Z ≃g SimpleGraph.pathGraph n))
    (sustainable_gts_step (V := Fin n))
    (fun Z : SimpleGraph (Fin n) =>
      (Finset.univ.filter (fun W : SimpleGraph (Fin n) =>
        adjacency_spectral_radius W < adjacency_spectral_radius Z)).card) ?_ X hX
  intro Z hZsus hZ
  obtain ⟨Y, hYsus, hgts, hlt⟩ := hstep n hn Z hZsus hZ
  exact ⟨Y, hYsus, card_filter_lt_card_filter_of_lt
    (fun W : SimpleGraph (Fin n) => adjacency_spectral_radius W) hlt,
    hYsus, hZsus, hgts⟩
