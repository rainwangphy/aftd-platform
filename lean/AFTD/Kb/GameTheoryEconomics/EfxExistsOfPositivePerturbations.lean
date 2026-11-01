import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_exists_of_positive_perturbations

Topic: fair_division   Node: 1a8624a37ee6

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For any finite real additive valuation profile, if adding every strictly positive common real epsilon to every item value admits a complete EFX allocation, then the original profile admits a complete EFX allocation.
-/

open Function Finset

theorem efx_exists_of_positive_perturbations {m n : ℕ} (u : Fin n → Fin m → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ σ : Fin m → Fin n,
      is_efx_goods (fun i g => u i g + ε) σ) :
    ∃ σ : Fin m → Fin n, is_efx_goods u σ := by
  classical
  have hσ (σ : Fin m → Fin n) :
      IsClosed {ε : ℝ | is_efx_goods (fun i g => u i g + ε) σ} := by
    simp only [is_efx_goods, Set.ofPred_forall]
    refine isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
      (fun hij => isClosed_iInter (fun g => isClosed_iInter (fun hg => ?_)))))
    dsimp [additive_valuation]
    apply isClosed_le <;> fun_prop
  have hC : IsClosed {ε : ℝ | ∃ σ : Fin m → Fin n,
      is_efx_goods (fun i g => u i g + ε) σ} := by
    simp only [Set.ofPred_exists]
    exact isClosed_iUnion_of_finite hσ
  have hz : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hh := (closure_minimal (show Set.Ioi (0 : ℝ) ⊆ {ε : ℝ | ∃ σ : Fin m → Fin n,
      is_efx_goods (fun i g => u i g + ε) σ} from h) hC) hz
  change ∃ σ : Fin m → Fin n, is_efx_goods (fun i g => u i g + 0) σ at hh
  simpa only [add_zero] using hh
