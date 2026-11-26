import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFefx
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# fefx_implies_strong_fef1

Topic: fair_division   Node: 813ed08e4cb4

Provenance: helper lemma. arXiv:2611.34488, Proposition 2.4

Every FEFx allocation satisfies strong FEF1: for any agent i and nonempty target D, any good g ∈ D witnesses strong FEF1 since every subset of D without g is a proper subset of D.
-/

/-- Every FEFx allocation satisfies strong FEF1. -/
theorem fefx_implies_strong_fef1 {m n : ℕ} (v : Fin n → Fin m → ℝ)
    (F : Fin n → Set (Finset (Fin m))) (A : Fin n → Finset (Fin m))
    (h : is_fefx v F A) : is_strong_fef1 v F A := by
  intro i D hD hne
  obtain ⟨g, hg⟩ := hne
  refine ⟨g, hg, ?_⟩
  intro T hT hTF
  exact h i D hD T ⟨hT.trans (Finset.erase_subset _ _),
    fun hDT => Finset.notMem_erase g D (hT (hDT hg))⟩ hTF
