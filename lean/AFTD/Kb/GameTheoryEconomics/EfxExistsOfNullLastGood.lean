import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxExistsOfUniversalLeastGood
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_exists_of_null_last_good

Topic: fair_division   Node: dcadf1b60f8b

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

For a positive number of agents and nonnegative additive values, a good worth zero to every agent can be added while retaining existence of a complete EFX allocation, with rearrangement allowed.
-/

open Function Finset

theorem efx_exists_of_null_last_good {m n : ℕ} (hn : 0 < n)
    (u : Fin n → Fin (m+1) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (hzero : ∀ i, u i (Fin.last m) = 0)
    (h : ∃ σ : Fin m → Fin n, is_efx_goods (fun i g => u i g.castSucc) σ) :
    ∃ τ : Fin (m+1) → Fin n, is_efx_goods u τ := by
  apply efx_exists_of_universal_least_good hn u hu _ h
  intro i g
  rw [hzero i]
  exact hu i g.castSucc
