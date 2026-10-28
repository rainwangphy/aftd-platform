import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxBundle
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_alpha_eefx_allocation

Topic: fair_division   Node: 10ff9312ff2c

Provenance: formalization of a published result. Source: arXiv:2610.34625 Def. 2.1

An allocation is alpha-EEFX if each agent's bundle is alpha-EEFX for that agent.
-/

/-- An allocation is alpha-EEFX if each agent's bundle is alpha-EEFX for that agent. -/
def is_alpha_eefx_allocation {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (α : ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i : Fin n, is_alpha_eefx_bundle (v i) n α (bundle_of σ i)
