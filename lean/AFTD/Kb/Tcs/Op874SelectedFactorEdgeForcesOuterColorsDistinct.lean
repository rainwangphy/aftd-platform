import AFTD.Prelude
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.CycleFactorHighColor
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor

/-!
# op874_selected_factor_edge_forces_outer_colors_distinct

Topic: graphs   Node: d5a1dacbecf7

Provenance: helper lemma. Local-state criterion for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Whenever a factor edge is selected by an unused low color at one end of a compatible two-versus-four local state, its two outer factor-edge colors are distinct, whether the endpoint bits agree or differ.
-/

theorem op874_selected_factor_edge_forces_outer_colors_distinct
    (n : ℕ) [NeZero n] (b : Fin n → Bool) (edge : Fin n → Fin 4)
    (h : Fin n → Fin 3 → Fin 6) (i : Fin n)
    (hproper : ∀ j, edge (j-1) ≠ edge j)
    (hinj : ∀ j, Function.Injective (h j))
    (havoid : ∀ j p, h j p ≠ cycle_matching_low_color (b j) ∧
      h j p ≠ cycle_factor_high_color (edge (j-1)) ∧
      h j p ≠ cycle_factor_high_color (edge j))
    (hstrong : h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
      h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2)
    (hselected : h i 1 = cycle_matching_low_color (!b i) ∨
      h (i+1) 0 = cycle_matching_low_color (!b (i+1))) :
    edge (i-1) ≠ edge (i+1) := by
  classical
  intro heq
  let A := cycle_factor_high_color (edge (i-1))
  let B := cycle_factor_high_color (edge i)
  have hAB : A ≠ B := by
    intro hh
    apply hproper i
    apply Fin.ext
    have hv := congrArg Fin.val hh
    dsimp [A,B,cycle_factor_high_color] at hv
    omega
  have hlowA : ∀ t : Bool, cycle_matching_low_color t ≠ A := by
    intro t hh
    have hv := congrArg Fin.val hh
    cases t <;> simp [cycle_matching_low_color,A,cycle_factor_high_color] at hv
  have hlowB : ∀ t : Bool, cycle_matching_low_color t ≠ B := by
    intro t hh
    have hv := congrArg Fin.val hh
    cases t <;> simp [cycle_matching_low_color,B,cycle_factor_high_color] at hv
  have ha0 : h i 0 ≠ A := (havoid i 0).2.1
  have hb0 : h i 0 ≠ B := (havoid i 0).2.2
  have ha2 : h i 2 ≠ A := (havoid i 2).2.1
  have hb2 : h i 2 ≠ B := (havoid i 2).2.2
  have hc1 : h (i+1) 1 ≠ A := by
    have hh := (havoid (i+1) 1).2.2
    simpa [A, ← heq] using hh
  have hc2 : h (i+1) 2 ≠ A := by
    have hh := (havoid (i+1) 2).2.2
    simpa [A, ← heq] using hh
  have hd1 : h (i+1) 1 ≠ B := by
    have hh := (havoid (i+1) 1).2.1
    simpa [B] using hh
  have hd2 : h (i+1) 2 ≠ B := by
    have hh := (havoid (i+1) 2).2.1
    simpa [B] using hh
  have hu : h i 0 ≠ h i 2 := fun hh => (by decide : (0 : Fin 3) ≠ 2) ((hinj i) hh)
  have hv : h (i+1) 1 ≠ h (i+1) 2 := fun hh => (by decide : (1 : Fin 3) ≠ 2) ((hinj (i+1)) hh)
  have impossible (t : Bool)
      (hu0 : h i 0 ≠ cycle_matching_low_color t)
      (hu2 : h i 2 ≠ cycle_matching_low_color t)
      (hv1 : h (i+1) 1 ≠ cycle_matching_low_color t)
      (hv2 : h (i+1) 2 ≠ cycle_matching_low_color t) : False := by
    have hh := equal_external_triple_forces_shared_exposed_color
      (cycle_matching_low_color t) A B (h i 0) (h i 2) (h (i+1) 1) (h (i+1) 2)
      (hlowA t) (hlowB t) hAB ⟨hu0,ha0,hb0⟩ ⟨hu2,ha2,hb2⟩
      ⟨hv1,hc1,hd1⟩ ⟨hv2,hc2,hd2⟩ hu hv
    rcases hh with hh | hh | hh | hh
    · exact hstrong.1 hh
    · exact hstrong.2.1 hh
    · exact hstrong.2.2.1 hh
    · exact hstrong.2.2.2 hh
  by_cases hb : b i = b (i+1)
  · apply impossible (b i)
    · exact (havoid i 0).1
    · exact (havoid i 2).1
    · simpa [hb] using (havoid (i+1) 1).1
    · simpa [hb] using (havoid (i+1) 2).1
  · have hl : cycle_matching_low_color (!b i) = cycle_matching_low_color (b (i+1)) := by
      cases hbi : b i <;> cases hbj : b (i+1) <;> simp_all [cycle_matching_low_color]
    have hr : cycle_matching_low_color (!(b (i+1))) = cycle_matching_low_color (b i) := by
      cases hbi : b i <;> cases hbj : b (i+1) <;> simp_all [cycle_matching_low_color]
    rcases hselected with hs | hs
    · apply impossible (b (i+1))
      · have hh : h i 0 ≠ h i 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) ((hinj i) he)
        simpa [hs,hl] using hh
      · have hh : h i 2 ≠ h i 1 := fun he => (by decide : (2 : Fin 3) ≠ 1) ((hinj i) he)
        simpa [hs,hl] using hh
      · exact (havoid (i+1) 1).1
      · exact (havoid (i+1) 2).1
    · apply impossible (b i)
      · exact (havoid i 0).1
      · exact (havoid i 2).1
      · have hh : h (i+1) 1 ≠ h (i+1) 0 := fun he => (by decide : (1 : Fin 3) ≠ 0) ((hinj (i+1)) he)
        simpa [hs,hr] using hh
      · have hh : h (i+1) 2 ≠ h (i+1) 0 := fun he => (by decide : (2 : Fin 3) ≠ 0) ((hinj (i+1)) he)
        simpa [hs,hr] using hh
