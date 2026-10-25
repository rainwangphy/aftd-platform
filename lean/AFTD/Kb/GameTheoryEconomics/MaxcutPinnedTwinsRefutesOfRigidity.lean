import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeStableColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutPinnedTwinsDisplayedDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityColorPermutation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutHasOptimalStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_pinned_twins_refutes_of_rigidity

Topic: equilibria   Node: 3c7e616de680

Provenance: helper lemma. Conditional refutation criterion for OP-89. The displayed deviation is Lean checked; all-optimum rigidity of this graph remains unproved. This conditional theorem does not settle OP-89.

If every optimum of the explicit pinned-twin graph is its displayed initial coloring up to a global color permutation, then this graph has no optimal strong equilibrium.
-/

private instance maxcut_pinned_twins_refutes_of_rigidity_pinned_graph_decidable : DecidableRel maxcut_pinned_twins_graph.Adj := by
  unfold maxcut_pinned_twins_graph
  infer_instance

theorem maxcut_pinned_twins_refutes_of_rigidity
    (h : ∀ ρ : ((Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) → Fin 3,
      is_maxcut_optimal maxcut_pinned_twins_graph ρ →
      ∃ p : Equiv.Perm (Fin 3),
        ρ = fun v => p (maxcut_anchor_three_initial_coloring v.1)) :
    ¬ maxcut_has_optimal_strong_equilibrium maxcut_pinned_twins_graph 3 := by
  rintro ⟨σ, h_opt, h_eq⟩
  obtain ⟨p, rfl⟩ := h σ h_opt
  obtain ⟨h_ne, h_out, h_in⟩ := maxcut_pinned_twins_displayed_deviation.2
  set S : Finset (((Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2)) := Finset.univ.filter (fun v => v.1.isLeft)
  set τ := fun v : ((Fin 16 ⊕ (Fin 3 × Fin 25)) × Fin 2) => p (maxcut_anchor_three_stable_coloring v.1)
  have h_dev_p : is_maxcut_strong_deviation maxcut_pinned_twins_graph
      (fun v => p (maxcut_anchor_three_initial_coloring v.1)) S τ := by
    refine ⟨h_ne, ?_, ?_⟩
    · intro v hv
      dsimp [τ]
      have hv_eq := h_out v hv
      dsimp at hv_eq
      rw [hv_eq]
    · intro v hv
      rw [maxcut_utility_color_permutation maxcut_pinned_twins_graph (fun w => maxcut_anchor_three_initial_coloring w.1) p v]
      rw [maxcut_utility_color_permutation maxcut_pinned_twins_graph (fun w => maxcut_anchor_three_stable_coloring w.1) p v]
      exact h_in v hv
  exact h_eq S τ h_dev_p
