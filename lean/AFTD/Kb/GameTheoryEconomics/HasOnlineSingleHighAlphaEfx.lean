import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOnlineAllocator
import AFTD.Kb.GameTheoryEconomics.IsSingleHighProfile
import AFTD.Kb.GameTheoryEconomics.IsAlphaEfxGoods

/-!
# has_online_single_high_alpha_efx

Topic: fair_division   Node: 471bd74deb32

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 4

There exists a deterministic online allocation algorithm for n agents and m goods that guarantees an alpha-EFX allocation for every single-high valuation profile with ratio R.
-/

/-- There exists a deterministic online allocation algorithm for n agents and m goods that guarantees an alpha-EFX allocation for every single-high valuation profile with ratio R. -/
def has_online_single_high_alpha_efx (n m : ℕ) (R α : ℝ) : Prop := ∃ alg : (Fin n → Fin m → ℝ) → (Fin m → Fin n),
    is_online_allocator n m alg ∧
    ∀ v : Fin n → Fin m → ℝ, is_single_high_profile R v →
      is_alpha_efx_goods v α (alg v)
