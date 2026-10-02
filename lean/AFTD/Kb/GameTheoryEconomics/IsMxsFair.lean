import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxFair
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_mxs_fair

Topic: fair_division   Node: 8b18eb786997

An allocation is MXS-fair to agent i (minimum EFX share, Garg-Sharma Def. 10) if i's bundle is worth to her at least her bundle in some allocation that is EFX-fair to her.
-/

/-- Minimum EFX share (Garg-Sharma Def. 10 with F = EFX, equal entitlements): agent `i`'s bundle under `σ` is worth to her at least her bundle in some allocation `τ` that is EFX-fair to her. -/
def is_mxs_fair {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) (i : Fin n) : Prop :=
  ∃ τ : Fin m → Fin n, is_efx_fair v τ i ∧ v i (bundle_of τ i) ≤ v i (bundle_of σ i)
