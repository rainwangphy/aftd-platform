import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IrrStep
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# irr_step_changed_agent_strict

Topic: fair_division   Node: 2c6d15331358

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

Every irr_step is carried out by a single agent i: her new bid b' i is an admissible bid for her at b, nothing but her own bid changes (b' = Function.update b i (b' i)), and the additive value of her own picking-sequence bundle strictly increases.
-/

/-- An irr_step is a single-agent bid change to an admissible best response that strictly raises the mover's own bundle value. -/
theorem irr_step_changed_agent_strict {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (v : N → G → ℝ) (seq : List N) (adm : (N → Fin m ≃ G) → N → (Fin m ≃ G) → Prop)
    (b b' : N → Fin m ≃ G) (h : irr_step v seq adm b b') :
    ∃ i, adm b i (b' i) ∧ b' = Function.update b i (b' i) ∧
      ∑ g ∈ picking_sequence_outcome seq b i, v i g
        < ∑ g ∈ picking_sequence_outcome seq b' i, v i g := by
  obtain ⟨i, ⟨r₁, _hr₁adm, hr₁⟩, r₂, hr₂adm, hb', hbr⟩ := h
  have hbi : b' i = r₂ := by rw [hb']; simp
  refine ⟨i, ?_, ?_, ?_⟩
  · show adm b i (b' i)
    rw [hbi]; exact hr₂adm
  · show b' = Function.update b i (b' i)
    rw [hbi]; exact hb'
  · show ∑ g ∈ picking_sequence_outcome seq b i, v i g
        < ∑ g ∈ picking_sequence_outcome seq b' i, v i g
    have h1 : ∑ g ∈ picking_sequence_outcome seq (Function.update b i r₁) i, v i g
        ≤ ∑ g ∈ picking_sequence_outcome seq b' i, v i g := hbr r₁ _hr₁adm
    linarith
