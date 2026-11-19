import AFTD.Prelude
import AFTD.Kb.Tcs.RetainedLineMsfWeight
import AFTD.Kb.Tcs.GraphCost

/-!
# retained_line_msf_weight_empty

Topic: algorithms   Node: c17a3d4f5e9e

Provenance: helper lemma. Sanity check for retained_line_msf_weight for OP-815.

The minimum spanning forest of the empty graph on n line vertices has total weight zero.
-/

theorem retained_line_msf_weight_empty (n : ℕ) : retained_line_msf_weight (⊥ : SimpleGraph (Fin n)) = 0 := by
  classical
  simp only [retained_line_msf_weight]
  have h : {x : ℝ | ∃ F : SimpleGraph (Fin n),
    Maximal (fun H : SimpleGraph (Fin n) => H ≤ (⊥ : SimpleGraph (Fin n)) ∧ H.IsAcyclic) F ∧
    x = graph_cost (fun i j => |(i.val : ℝ) - (j.val : ℝ)|) F} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hf : F = ⊥ := le_bot_iff.mp hF.1.1
      subst F
      simp [graph_cost]
    · intro hx
      subst x
      refine ⟨⊥, ?_, ?_⟩
      · refine ⟨⟨le_refl _, SimpleGraph.isAcyclic_bot⟩, ?_⟩
        intro b hb _
        exact hb.1
      · simp [graph_cost]
  rw [h, csInf_singleton]
