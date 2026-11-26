import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1
import AFTD.Kb.GameTheoryEconomics.IsFef1
import AFTD.Kb.GameTheoryEconomics.IsHereditary
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# strong_fef1_implies_fef1

Topic: fair_division   Node: a3d4e93f35a6

Provenance: helper lemma. arXiv:2611.34488, Proposition 2.4

For nonnegative additive valuations and hereditary feasible families, every allocation satisfying strong FEF1 is FEF1.
-/

/-- Every strong FEF1 allocation is FEF1 under nonnegative additive valuations and hereditary feasibility. -/
theorem strong_fef1_implies_fef1 {m n : ℕ} (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g)
    (F : Fin n → Set (Finset (Fin m)))
    (hF : ∀ i, is_hereditary (F i))
    (A : Fin n → Finset (Fin m))
    (h : is_strong_fef1 v F A) : is_fef1 v F A := by
  intro i D hD T hTD hTne hTF
  obtain ⟨x0, hx0⟩ := hTne
  have hDne : D.Nonempty := ⟨x0, hTD hx0⟩
  rcases h i D hD hDne with ⟨g, hgD, hg⟩
  by_cases hgT : g ∈ T
  · refine ⟨g, hgT, ?_⟩
    exact hg (T.erase g) (Finset.erase_subset_erase g hTD)
      ((hF i).2 hTF (Finset.erase_subset g T))
  · refine ⟨x0, hx0, ?_⟩
    have hTD' : T ⊆ D.erase g := by
      rw [Finset.subset_erase]; exact ⟨hTD, hgT⟩
    have hle : additive_valuation (v i) T ≤ additive_valuation (v i) (A i) := hg T hTD' hTF
    have hle2 : additive_valuation (v i) (T.erase x0) ≤ additive_valuation (v i) T :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset x0 T) (fun y _ _ => hv i y)
    linarith
