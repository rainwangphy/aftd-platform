import AFTD.Prelude
import AFTD.Kb.Tcs.RelationReachesTerminalOfNatRankAscent
import AFTD.Kb.Tcs.CardFilterGtCardFilterOfLt
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.NonsustainableGtsStep
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsGeneralizedTreeShift

/-!
# nonsustainable_star_connectivity_of_ascent_step

Topic: graphs   Node: 9ce1f3194ee8

Provenance: helper lemma. step towards op223_poset_connectivity

If every non-sustainable tree on Fin n (n ≥ 2) that is not a star has a non-sustainable generalized-tree-shift successor with strictly larger adjacency spectral radius, then every non-sustainable tree on Fin n reaches some graph isomorphic to the star completeBipartiteGraph (Fin 1) (Fin (n-1)) by a sequence of non-sustainable generalized tree shifts. This is the second conjunct of op223_poset_connectivity with the one-step ascent claim isolated as a hypothesis.
-/

/-- The non-sustainable half of op223_poset_connectivity follows from the one-step ascent claim plus finite ascent on the spectral rank #{W | λ Z < λ W}. -/
theorem nonsustainable_star_connectivity_of_ascent_step
    (hstep : ∀ (n : ℕ) (_hn : 2 ≤ n) (X : SimpleGraph (Fin n)), is_nonsustainable_tree X →
      ¬ Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) →
      ∃ Y : SimpleGraph (Fin n), is_nonsustainable_tree Y ∧ is_generalized_tree_shift X Y ∧
        adjacency_spectral_radius X < adjacency_spectral_radius Y) :
    ∀ (n : ℕ) (_hn : 2 ≤ n) (X : SimpleGraph (Fin n)), is_nonsustainable_tree X →
      ∃ S : SimpleGraph (Fin n), Nonempty (S ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) ∧
        Relation.ReflTransGen nonsustainable_gts_step X S := by
  intro n hn X hX
  classical
  refine relation_reaches_terminal_of_nat_rank_ascent
    (fun Z : SimpleGraph (Fin n) => is_nonsustainable_tree Z)
    (fun Z : SimpleGraph (Fin n) =>
      Nonempty (Z ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))))
    (nonsustainable_gts_step (V := Fin n))
    (fun Z : SimpleGraph (Fin n) =>
      (Finset.univ.filter (fun W : SimpleGraph (Fin n) =>
        adjacency_spectral_radius Z < adjacency_spectral_radius W)).card) ?_ X hX
  intro Z hZns hZ
  obtain ⟨Y, hYns, hgts, hlt⟩ := hstep n hn Z hZns hZ
  exact ⟨Y, hYns, card_filter_gt_card_filter_of_lt (fun W : SimpleGraph (Fin n) =>
    adjacency_spectral_radius W) hlt, hZns, hYns, hgts⟩
