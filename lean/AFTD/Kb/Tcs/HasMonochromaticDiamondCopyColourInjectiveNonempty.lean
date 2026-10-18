import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# has_monochromatic_diamond_copy_colour_injective_nonempty

Topic: combinatorics   Node: 3b5c284f4da0

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

If ψ = f ∘ χ on nonempty sets (f injective) and ψ ∅ ≠ f col, then a monochromatic induced j-diamond in ψ of colour f col yields one in χ of colour col.
-/

/-- Diamond copies transfer along an injective relabelling of colours that is honest only off the empty set, given that the empty set carries a different colour. -/
theorem has_monochromatic_diamond_copy_colour_injective_nonempty {j d k k' : ℕ} (f : Fin k → Fin k')
    (hf : Function.Injective f) (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (ψ : Finset (Fin d) → Fin k') (h : ∀ A, A.Nonempty → ψ A = f (χ A))
    (hempty : ψ ∅ ≠ f col) :
    has_monochromatic_diamond_copy j d (f col) ψ → has_monochromatic_diamond_copy j d col χ := by
  rintro ⟨bot, top, hbot_top, hψ_bot, hψ_top, mid, hmid, hmid_inc⟩
  have hbot_ne : bot ≠ ∅ := fun he => hempty (he ▸ hψ_bot)
  have hbot_nonempty : bot.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbot_ne
  have htop_nonempty : top.Nonempty := hbot_nonempty.mono hbot_top.1
  have hcol : ∀ {A}, A.Nonempty → ψ A = f col → χ A = col :=
    fun hA hψ => hf ((h _ hA).symm.trans hψ)
  refine ⟨bot, top, hbot_top, hcol hbot_nonempty hψ_bot, hcol htop_nonempty hψ_top, mid, fun i => ?_, hmid_inc⟩
  obtain ⟨h1, h2, h3⟩ := hmid i
  exact ⟨h1, h2, hcol (hbot_nonempty.mono h1.1) h3⟩
