import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# has_monochromatic_fan_copy_colour_injective_nonempty

Topic: combinatorics   Node: 3123ae8b6584

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

For j ≥ 2, if ψ = f ∘ χ on nonempty sets (f injective), then a monochromatic induced F_j in ψ of colour f col yields one in χ of colour col.
-/

/-- Fan copies transfer along an injective relabelling of colours that is honest only off the empty set; fan copies use only nonempty sets when j ≥ 2. -/
theorem has_monochromatic_fan_copy_colour_injective_nonempty {j d k k' : ℕ} (hj : 2 ≤ j)
    (f : Fin k → Fin k') (hf : Function.Injective f) (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (ψ : Finset (Fin d) → Fin k') (h : ∀ A, A.Nonempty → ψ A = f (χ A)) :
    has_monochromatic_fan_copy j d (f col) ψ → has_monochromatic_fan_copy j d col χ := by
  intro hψ
  unfold has_monochromatic_fan_copy at hψ ⊢
  rcases hψ with ⟨top, htop, mid, hmid, hinc⟩
  have htop_ne : top.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsub : mid ⟨0, by omega⟩ ⊆ top := (hmid ⟨0, by omega⟩).1.1
    rw [hne] at hsub
    have heq : mid ⟨0, by omega⟩ = ∅ := Finset.subset_empty.mp hsub
    exact (hmid ⟨0, by omega⟩).1.2 (by rw [hne, heq])
  have hmid_ne : ∀ i, (mid i).Nonempty := by
    intro i
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i', hi'⟩ : ∃ i' : Fin j, i' ≠ i := by
      by_cases hi0 : i = ⟨0, by omega⟩
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [hi0]
        simp [Fin.ext_iff]
      · exact ⟨⟨0, by omega⟩, fun hh => hi0 hh.symm⟩
    have hsub : mid i ⊆ mid i' := by rw [hne]; exact Finset.empty_subset _
    exact hinc i i' hi'.symm hsub
  refine ⟨top, ?_, mid, ?_, hinc⟩
  · have h1 : ψ top = f (χ top) := h top htop_ne
    rw [h1] at htop
    exact hf htop
  · intro i
    refine ⟨(hmid i).1, ?_⟩
    have h1 : ψ (mid i) = f (χ (mid i)) := h (mid i) (hmid_ne i)
    have h2 : ψ (mid i) = f col := (hmid i).2
    rw [h1] at h2
    exact hf h2
