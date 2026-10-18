import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# has_monochromatic_diamond_copy_colour_injective

Topic: combinatorics   Node: 4944b8834e71

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Relabelling colours by an injective map does not change the existence of a monochromatic induced j-diamond: if ψ = f ∘ χ with f injective, then χ has a mono j-diamond in colour col iff ψ has one in colour f col.
-/

/-- Diamond copies transfer along an injective relabelling of the colour type. -/
theorem has_monochromatic_diamond_copy_colour_injective {j d k k' : ℕ} (f : Fin k → Fin k')
    (hf : Function.Injective f) (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (ψ : Finset (Fin d) → Fin k') (h : ∀ A, ψ A = f (χ A)) :
    has_monochromatic_diamond_copy j d (f col) ψ ↔ has_monochromatic_diamond_copy j d col χ := by
  simp only [has_monochromatic_diamond_copy, h, hf.eq_iff]
