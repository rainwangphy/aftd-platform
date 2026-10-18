import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# has_monochromatic_fan_copy_colour_injective

Topic: combinatorics   Node: 26ebef39f71b

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Relabelling colours by an injective map does not change the existence of a monochromatic induced F_j: if ψ = f ∘ χ with f injective, then χ has a mono F_j in colour col iff ψ has one in colour f col.
-/

/-- Fan copies transfer along an injective relabelling of the colour type. -/
theorem has_monochromatic_fan_copy_colour_injective {j d k k' : ℕ} (f : Fin k → Fin k')
    (hf : Function.Injective f) (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (ψ : Finset (Fin d) → Fin k') (h : ∀ A, ψ A = f (χ A)) :
    has_monochromatic_fan_copy j d (f col) ψ ↔ has_monochromatic_fan_copy j d col χ := by
  unfold has_monochromatic_fan_copy
  constructor
  · rintro ⟨top, htop, mid, hmid, hinc⟩
    refine ⟨top, hf ?_, mid, ?_, hinc⟩
    · rw [h top] at htop; exact htop
    · intro i
      exact ⟨(hmid i).1, hf (by rw [← h (mid i)]; exact (hmid i).2)⟩
  · rintro ⟨top, htop, mid, hmid, hinc⟩
    refine ⟨top, ?_, mid, ?_, hinc⟩
    · rw [h top, htop]
    · intro i
      exact ⟨(hmid i).1, by rw [h (mid i), (hmid i).2]⟩
