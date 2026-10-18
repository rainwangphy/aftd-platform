import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopyColourInjective
import AFTD.Kb.Tcs.HasMonochromaticFanCopyColourInjective
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# mixed_diamond_fan_ramsey_bound_last_colour_step

Topic: combinatorics   Node: 0af1fd33f7f2

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Case b = 0, a ≥ 1: if d ≥ j*a and the statement holds at (a-1, 1) in the same dimension, then every colouring with a colours has a monochromatic induced j-diamond in one of them.
-/

theorem mixed_diamond_fan_ramsey_bound_last_colour_step_fan_to_diamond
    (j d : ℕ) (hj : 2 ≤ j) {k : ℕ} (c : Fin k)
    (χ : Finset (Fin d) → Fin k) (h0 : χ ∅ = c)
    (hfan : has_monochromatic_fan_copy j d c χ) :
    has_monochromatic_diamond_copy j d c χ := by
  have : NeZero j := ⟨by omega⟩
  obtain ⟨top, htop, mid, hmid, hpair⟩ := hfan
  have key : ∀ i : Fin j, mid i ≠ ∅ := by
    intro i hi
    have hne : ∃ i' : Fin j, i' ≠ i := by
      rcases eq_or_ne i 0 with h | h
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [h]
        intro hh
        have hv := congrArg Fin.val hh
        simp at hv
      · exact ⟨0, fun hh => h hh.symm⟩
    obtain ⟨i', hi'⟩ := hne
    exact hpair i i' (Ne.symm hi') (by rw [hi]; exact Finset.empty_subset _)
  refine ⟨∅, top, ?_, h0, htop, mid, ?_, hpair⟩
  · exact lt_trans (Finset.empty_ssubset.mpr (Finset.nonempty_iff_ne_empty.mpr (key 0)))
      (hmid 0).1
  · intro i
    exact ⟨Finset.empty_ssubset.mpr (Finset.nonempty_iff_ne_empty.mpr (key i)),
      (hmid i).1, (hmid i).2⟩

/-- b = 0 step: recolour the colour of ∅ as the single fan colour and apply the (a-1, 1) instance; a fan in that colour plus ∅ as bottom is a diamond. -/
theorem mixed_diamond_fan_ramsey_bound_last_colour_step (j a d : ℕ) (hj : 2 ≤ j) (ha : 1 ≤ a)
    (hd : j * a ≤ d) (ih : mixed_ramsey_property j (a - 1) 1 d) : mixed_ramsey_property j a 0 d := by
  intro χ
  have ha' : a = (a - 1) + 1 := by omega
  let c₀ : Fin a := χ ∅
  let e₀ : Fin a ≃ Fin ((a - 1) + 1) := (Fin.castOrderIso ha').toEquiv
  let e : Fin a ≃ Fin ((a - 1) + 1) := e₀.trans (Equiv.swap (e₀ c₀) (Fin.last (a - 1)))
  have he_c₀ : e c₀ = Fin.last (a - 1) := by
    show (Equiv.swap (e₀ c₀) (Fin.last (a - 1))) (e₀ c₀) = Fin.last (a - 1)
    exact Equiv.swap_apply_left _ _
  let κ : Finset (Fin d) → Fin ((a - 1) + 1) := fun A => e (χ A)
  have hκ : ∀ A, κ A = e (χ A) := fun A => rfl
  rcases ih κ with ⟨col, hcol⟩ | ⟨col, hcol⟩
  · left
    have hdiam : has_monochromatic_diamond_copy j d (e.symm (Fin.castAdd 1 col)) χ := by
      refine (has_monochromatic_diamond_copy_colour_injective (j := j) e e.injective
        (e.symm (Fin.castAdd 1 col)) χ κ hκ).mp ?_
      rwa [Equiv.apply_symm_apply]
    refine ⟨e.symm (Fin.castAdd 1 col), ?_⟩
    have heq : Fin.castAdd 0 (e.symm (Fin.castAdd 1 col))
        = e.symm (Fin.castAdd 1 col) := rfl
    rw [heq]
    exact hdiam
  · left
    have hcol0 : (Fin.natAdd (a - 1) col) = e c₀ := by
      have hc : col = 0 := by ext; omega
      rw [hc, he_c₀]
      apply Fin.ext
      simp [Fin.last]
    have hfan : has_monochromatic_fan_copy j d c₀ χ := by
      refine (has_monochromatic_fan_copy_colour_injective (j := j) e e.injective c₀ χ κ hκ).mp ?_
      rw [← hcol0]
      exact hcol
    exact ⟨c₀, mixed_diamond_fan_ramsey_bound_last_colour_step_fan_to_diamond j d hj c₀ χ rfl hfan⟩
