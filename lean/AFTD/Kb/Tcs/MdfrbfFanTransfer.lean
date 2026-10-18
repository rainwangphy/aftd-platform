import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# mdfrbf_fan_transfer

Topic: combinatorics   Node: 49b1793c54fa

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Push-forward of a monochromatic fan along an order embedding of set systems: if j ≥ 2, T is injective, monotone and reflects inclusions, χ (T A) = f (ψ A) on nonempty A, and ψ has a monochromatic F_j in colour col, then χ has a monochromatic F_j in colour f col.
-/

/-- Transfers a monochromatic fan copy across an order embedding T of set systems (colour change f). -/
theorem mdfrbf_fan_transfer {j K d k k' : ℕ} (hj : 2 ≤ j) (f : Fin k → Fin k')
    (T : Finset (Fin K) → Finset (Fin d)) (hT : ∀ A A', T A ⊆ T A' ↔ A ⊆ A')
    (χ : Finset (Fin d) → Fin k') (ψ : Finset (Fin K) → Fin k)
    (h : ∀ A, A.Nonempty → χ (T A) = f (ψ A)) (col : Fin k) :
    has_monochromatic_fan_copy j K col ψ → has_monochromatic_fan_copy j d (f col) χ := by
  rintro ⟨top, htopc, mid, hmid, hincomp⟩
  have hinj : Function.Injective T := fun A A' hh =>
    Finset.Subset.antisymm ((hT A A').mp (le_of_eq hh)) ((hT A' A).mp (le_of_eq hh.symm))
  have hmidne : ∀ i : Fin j, (mid i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have hpos : 0 < (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i', hi'⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_erase] at hi'
    exact hincomp i i' hi'.1.symm (by rw [h0]; exact Finset.empty_subset _)
  have htopne : top.Nonempty :=
    Finset.Nonempty.mono (hmid ⟨0, by omega⟩).1.1 (hmidne ⟨0, by omega⟩)
  refine ⟨T top, ?_, fun i => T (mid i), ?_, ?_⟩
  · rw [h top htopne, htopc]
  · intro i
    refine ⟨?_, ?_⟩
    · rw [Finset.ssubset_iff_subset_ne]
      exact ⟨(hT (mid i) top).mpr (hmid i).1.1, fun heq => (hmid i).1.2 (le_of_eq (hinj heq).symm)⟩
    · rw [h (mid i) (hmidne i), (hmid i).2]
  · intro i i' hne hincl
    exact hincomp i i' hne ((hT (mid i) (mid i')).mp hincl)
