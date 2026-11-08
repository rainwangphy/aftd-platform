import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TorusGraph
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategy
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategySuccessful
import AFTD.Kb.GameTheoryEconomics.ClosedNeighborhood
import AFTD.Kb.GameTheoryEconomics.ThreeByCycleTorusMovingTargetAccuracyLeCeil

/-!
# three_by_three_torus_moving_target_accuracy_exact

Topic: combinatorial_games   Node: 0808dadaa80c

Provenance: helper lemma. three_by_cycle_torus_moving_target_accuracy_exact

On the 3-by-3 torus C_3 □ C_3, the minimum achievable moving-target localization accuracy starting from the candidate set of all vertices is exactly 5.
-/

theorem three_by_three_torus_moving_target_accuracy_exact_expansion_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℕ)
    (h_exp : ∀ D : Finset V, K ≤ D.card → 2 * K ≤ (closed_neighborhood G D).card + 1)
    (S : MovingTargetStrategy V) :
    ∀ (D : Finset V) (s : ℕ), K ≤ D.card →
      moving_target_strategy_successful G s S D → K ≤ s := by
  induction' S with Q on_false on_true ih_false ih_true
  · intro D s hD hsucc
    simp only [moving_target_strategy_successful] at hsucc
    exact le_trans hD hsucc
  · intro D s hD hsucc
    simp only [moving_target_strategy_successful] at hsucc
    rcases hsucc with ⟨h_false, h_true⟩
    by_cases hK : K = 0
    · subst hK; exact Nat.zero_le s
    have hexp := h_exp D hD
    have hsum : (closed_neighborhood G D \ Q).card + (closed_neighborhood G D ∩ Q).card =
        (closed_neighborhood G D).card := Finset.card_sdiff_add_card_inter (closed_neighborhood G D) Q
    have hor : K ≤ (closed_neighborhood G D \ Q).card ∨ K ≤ (closed_neighborhood G D ∩ Q).card := by
      by_contra! h
      omega
    rcases hor with hleft | hright
    · have hne : (closed_neighborhood G D \ Q).Nonempty := Finset.card_pos.mp (by omega)
      exact ih_false _ s hleft (h_false hne)
    · have hne : (closed_neighborhood G D ∩ Q).Nonempty := Finset.card_pos.mp (by omega)
      exact ih_true _ s hright (h_true hne)

theorem three_by_three_torus_moving_target_accuracy_exact_neighborhood_expansion
    (D : Finset (Fin 3 × Fin 3)) (hD : 5 ≤ D.card) :
    2 * 5 ≤ (closed_neighborhood (torus_graph 3 3) D).card + 1 := by
  have h_univ : closed_neighborhood (torus_graph 3 3) D = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro v
    by_contra hv
    have h_sub : D ⊆ (Finset.univ.erase v.1) ×ˢ (Finset.univ.erase v.2) := by
      intro u hu
      rw [Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
      refine ⟨⟨?_, Finset.mem_univ _⟩, ⟨?_, Finset.mem_univ _⟩⟩
      · intro hu1
        apply hv
        rw [closed_neighborhood, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ⟨u, hu, ?_⟩⟩
        by_cases h2 : u.2 = v.2
        · left
          exact Prod.ext hu1 h2
        · right
          change (SimpleGraph.cycleGraph 3).Adj u.1 v.1 ∧ u.2 = v.2 ∨
                 (SimpleGraph.cycleGraph 3).Adj u.2 v.2 ∧ u.1 = v.1
          right
          refine ⟨?_, hu1⟩
          rw [SimpleGraph.cycleGraph_three_eq_top]
          exact h2
      · intro hu2
        apply hv
        rw [closed_neighborhood, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ⟨u, hu, ?_⟩⟩
        by_cases h1 : u.1 = v.1
        · left
          exact Prod.ext h1 hu2
        · right
          change (SimpleGraph.cycleGraph 3).Adj u.1 v.1 ∧ u.2 = v.2 ∨
                 (SimpleGraph.cycleGraph 3).Adj u.2 v.2 ∧ u.1 = v.1
          left
          refine ⟨?_, hu2⟩
          rw [SimpleGraph.cycleGraph_three_eq_top]
          exact h1
    have hcard : ((Finset.univ.erase v.1) ×ˢ (Finset.univ.erase v.2) : Finset (Fin 3 × Fin 3)).card = 4 := by
      rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    have hle := Finset.card_le_card h_sub
    rw [hcard] at hle
    omega
  rw [h_univ]
  simp

/-- The minimum achievable moving-target accuracy on C_3 □ C_3 is exactly 5. -/
theorem three_by_three_torus_moving_target_accuracy_exact :
    IsLeast {s : ℕ | ∃ S : MovingTargetStrategy (Fin 3 × Fin 3),
      moving_target_strategy_successful (torus_graph 3 3) s S Finset.univ} 5 := by
  refine ⟨?_, ?_⟩
  · change ∃ S, moving_target_strategy_successful (torus_graph 3 3) 5 S Finset.univ
    exact three_by_cycle_torus_moving_target_accuracy_le_ceil 3 (by norm_num)
  · rintro s ⟨S, hS⟩
    have huniv_card : (Finset.univ : Finset (Fin 3 × Fin 3)).card = 9 := by simp
    have hK_le : 5 ≤ (Finset.univ : Finset (Fin 3 × Fin 3)).card := by
      rw [huniv_card]
      omega
    exact three_by_three_torus_moving_target_accuracy_exact_expansion_lower_bound (torus_graph 3 3) 5
      three_by_three_torus_moving_target_accuracy_exact_neighborhood_expansion S Finset.univ s hK_le hS
