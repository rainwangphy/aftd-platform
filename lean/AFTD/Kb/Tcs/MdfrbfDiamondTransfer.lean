import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# mdfrbf_diamond_transfer

Topic: combinatorics   Node: 6f9a05b44c2f

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Push-forward of a monochromatic diamond along an order embedding of set systems: if T is injective, monotone and reflects inclusions on finsets, χ (T A) = f (ψ A) for every nonempty A, ψ ∅ ≠ col, and ψ has a monochromatic j-diamond in colour col, then χ has a monochromatic j-diamond in colour f col.
-/

/-- Transfers a monochromatic diamond copy across an order embedding T of set systems (colour change f). -/
theorem mdfrbf_diamond_transfer {j K d k k' : ℕ} (f : Fin k → Fin k')
    (T : Finset (Fin K) → Finset (Fin d)) (hT : ∀ A A', T A ⊆ T A' ↔ A ⊆ A')
    (χ : Finset (Fin d) → Fin k') (ψ : Finset (Fin K) → Fin k)
    (h : ∀ A, A.Nonempty → χ (T A) = f (ψ A)) (col : Fin k) (hempty : ψ ∅ ≠ col) :
    has_monochromatic_diamond_copy j K col ψ → has_monochromatic_diamond_copy j d (f col) χ := by
  rintro ⟨bot, top, hbot, hbotc, htopc, mid, hmid, hincomp⟩
  have hinj : Function.Injective T := fun A A' hh =>
    Finset.Subset.antisymm ((hT A A').mp (le_of_eq hh)) ((hT A' A).mp (le_of_eq hh.symm))
  have hbotne : bot.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0] at hbotc
    exact hempty hbotc
  have htopne : top.Nonempty := hbotne.mono hbot.1
  have hmidne : ∀ i : Fin j, (mid i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have hc := (hmid i).2.2
    rw [h0] at hc
    exact hempty hc
  refine ⟨T bot, T top, ?_, ?_, ?_, fun i => T (mid i), ?_, ?_⟩
  · rw [Finset.ssubset_iff_subset_ne]
    exact ⟨(hT bot top).mpr hbot.1, fun heq => hbot.2 (le_of_eq (hinj heq).symm)⟩
  · rw [h bot hbotne, hbotc]
  · rw [h top htopne, htopc]
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.ssubset_iff_subset_ne]
      exact ⟨(hT bot (mid i)).mpr (hmid i).1.1, fun heq => (hmid i).1.2 (le_of_eq (hinj heq).symm)⟩
    · rw [Finset.ssubset_iff_subset_ne]
      exact ⟨(hT (mid i) top).mpr (hmid i).2.1.1, fun heq => (hmid i).2.1.2 (le_of_eq (hinj heq).symm)⟩
    · rw [h (mid i) (hmidne i), (hmid i).2.2]
  · intro i i' hne hincl
    exact hincomp i i' hne ((hT (mid i) (mid i')).mp hincl)
