import AFTD.Prelude
import AFTD.Kb.Tcs.IsCycleFactor

/-!
# cycleGraph_is_cycle_factor

Topic: combinatorics   Node: ed29699d2691

Provenance: helper lemma. folklore

For any integer ℓ ≥ 3, the cycle graph of length ℓ is a C_ℓ-factor on its vertex set.
-/

/-- For any ℓ ≥ 3, the cycle graph of length ℓ is a C_ℓ-factor. -/
theorem cycleGraph_is_cycle_factor (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    is_cycle_factor (SimpleGraph.cycleGraph ℓ) ℓ := by
  have _ := hℓ
  intro c
  have hprec : (SimpleGraph.cycleGraph ℓ).Preconnected := SimpleGraph.cycleGraph_preconnected
  have hsupp : c.supp = (Set.univ : Set (Fin ℓ)) := by
    obtain ⟨w, rfl⟩ := c.exists_rep
    ext v
    simp only [Set.mem_univ, iff_true]
    exact SimpleGraph.ConnectedComponent.sound (hprec v w)
  have h1 : (SimpleGraph.cycleGraph ℓ).induce c.supp ≃g (SimpleGraph.cycleGraph ℓ).induce Set.univ := by
    rw [hsupp]
  exact ⟨h1.trans (SimpleGraph.induceUnivIso _)⟩
