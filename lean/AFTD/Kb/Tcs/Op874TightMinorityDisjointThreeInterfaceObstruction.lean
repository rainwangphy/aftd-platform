import AFTD.Prelude
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor
import AFTD.Kb.Tcs.Op874ContractionForcesEqualFactorPalette

/-!
# op874_tight_minority_disjoint_three_interface_obstruction

Topic: graphs   Node: 8be3f18eea25

Provenance: helper lemma. Tight-cut minority-palette obstruction for OP-874; https://arxiv.org/abs/2610.41950.

On the displayed six-cycle, requiring disjoint high palettes at the specified minority matching edge is incompatible with only the two indicated majority factor interfaces and one majority matching interface. Exact ownership, windows and the rest of the graph are not assumed.
-/

theorem op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five (c : Fin 4) : (5 : Fin 6) ≠ Fin.castAdd 2 c := by
  intro h
  have hv := congrArg Fin.val h
  have hw := c.isLt
  simp only [Fin.val_castAdd] at hv
  omega

theorem op874_tight_minority_disjoint_three_interface_obstruction_castAdd_inj {c d : Fin 4} (h : Fin.castAdd 2 c = Fin.castAdd 2 d) : c = d := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [Fin.val_castAdd] using hv

theorem op874_tight_minority_disjoint_three_interface_obstruction_exhaust_four (a b c d x : Fin 4)
    (hinj : Function.Injective ![a, c, d, b])
    (hxc : x ≠ c) (hxd : x ≠ d) : x = a ∨ x = b := by
  have hsurj : Function.Surjective ![a, c, d, b] :=
    (Fintype.bijective_iff_injective_and_card ![a, c, d, b]).mpr ⟨hinj, rfl⟩ |>.2
  obtain ⟨i, hi⟩ := hsurj x
  fin_cases i
  · left; rw [← hi]; rfl
  · exfalso; apply hxc; rw [← hi]; rfl
  · exfalso; apply hxd; rw [← hi]; rfl
  · right; rw [← hi]; rfl

theorem op874_tight_minority_disjoint_three_interface_obstruction :
    let bit : Fin 6 → Bool := ![false,true,true,true,false,true]
    ¬ ∃ (w : Fin 6 → Fin 4) (h : Fin 6 → Fin 3 → Fin 6),
      (∀ i, w (i-1) ≠ w i) ∧
      Function.Injective ![w 5,w 0,w 3,w 4] ∧
      (∀ i, Function.Injective (h i)) ∧
      (∀ i p, h i p ≠ (if bit i then 5 else 4) ∧
        h i p ≠ Fin.castAdd 2 (w (i-1)) ∧ h i p ≠ Fin.castAdd 2 (w i)) ∧
      (∀ i : Fin 6, (i = 1 ∨ i = 2) →
        h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
        h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2) ∧
      h 2 0 ≠ h 5 0 ∧ h 2 0 ≠ h 5 1 ∧
      h 2 1 ≠ h 5 0 ∧ h 2 1 ≠ h 5 1 := by
  intro bit hex
  obtain ⟨w, h, hproper, hmatch, hinj, hforbid, hinterface, hmatching⟩ := hex
  have hm1 : (1 : Fin 6) - 1 = 0 := by decide
  have hm2 : (2 : Fin 6) - 1 = 1 := by decide
  have hm3 : (3 : Fin 6) - 1 = 2 := by decide
  have hm5 : (5 : Fin 6) - 1 = 4 := by decide
  have hp1 : (1 : Fin 6) + 1 = 2 := by decide
  have hp2 : (2 : Fin 6) + 1 = 3 := by decide
  have hbit1 : bit 1 = true := rfl
  have hbit2 : bit 2 = true := rfl
  have hbit3 : bit 3 = true := rfl
  have hbit5 : bit 5 = true := rfl
  have hxc : w 1 ≠ w 0 := by
    have := hproper 1
    rw [hm1] at this
    exact this.symm
  have hxy : w 1 ≠ w 2 := by
    have := hproper 2
    rwa [hm2] at this
  have hyd : w 2 ≠ w 3 := by
    have := hproper 3
    rwa [hm3] at this
  have hyc : w 2 ≠ w 0 := by
    intro hyc_eq
    have h1forbid (p : Fin 3) : h 1 p ≠ 5 ∧ h 1 p ≠ Fin.castAdd 2 (w 0) ∧ h 1 p ≠ Fin.castAdd 2 (w 1) := by
      have hp := hforbid 1 p
      rw [hbit1] at hp
      simp only [ite_true] at hp
      rw [hm1] at hp
      exact hp
    have h2forbid (p : Fin 3) : h 2 p ≠ 5 ∧ h 2 p ≠ Fin.castAdd 2 (w 0) ∧ h 2 p ≠ Fin.castAdd 2 (w 1) := by
      have hp := hforbid 2 p
      rw [hbit2] at hp
      simp only [ite_true] at hp
      rw [hm2] at hp
      rw [hyc_eq] at hp
      exact ⟨hp.1, hp.2.2, hp.2.1⟩
    have hint1 := hinterface 1 (Or.inl rfl)
    rw [hp1] at hint1
    have h1pair : h 1 0 ≠ h 1 2 := fun e => (by decide : (0 : Fin 3) ≠ 2) (hinj 1 e)
    have h2pair : h 2 1 ≠ h 2 2 := fun e => (by decide : (1 : Fin 3) ≠ 2) (hinj 2 e)
    have hab : Fin.castAdd 2 (w 0) ≠ Fin.castAdd 2 (w 1) := fun e => hxc (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_inj e).symm
    have hmatch1 := equal_external_triple_forces_shared_exposed_color 5
      (Fin.castAdd 2 (w 0)) (Fin.castAdd 2 (w 1)) (h 1 0) (h 1 2) (h 2 1) (h 2 2)
      (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _)
      (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _) hab
      (h1forbid 0) (h1forbid 2) (h2forbid 1) (h2forbid 2) h1pair h2pair
    rcases hmatch1 with hm | hm | hm | hm
    · exact hint1.1 hm
    · exact hint1.2.1 hm
    · exact hint1.2.2.1 hm
    · exact hint1.2.2.2 hm
  have hxd : w 1 ≠ w 3 := by
    intro hxd_eq
    have h2forbid (p : Fin 3) : h 2 p ≠ 5 ∧ h 2 p ≠ Fin.castAdd 2 (w 3) ∧ h 2 p ≠ Fin.castAdd 2 (w 2) := by
      have hp := hforbid 2 p
      rw [hbit2] at hp
      simp only [ite_true] at hp
      rw [hm2] at hp
      rw [hxd_eq] at hp
      exact hp
    have h3forbid (p : Fin 3) : h 3 p ≠ 5 ∧ h 3 p ≠ Fin.castAdd 2 (w 3) ∧ h 3 p ≠ Fin.castAdd 2 (w 2) := by
      have hp := hforbid 3 p
      rw [hbit3] at hp
      simp only [ite_true] at hp
      rw [hm3] at hp
      exact ⟨hp.1, hp.2.2, hp.2.1⟩
    have hint2 := hinterface 2 (Or.inr rfl)
    rw [hp2] at hint2
    have h2pair : h 2 0 ≠ h 2 2 := fun e => (by decide : (0 : Fin 3) ≠ 2) (hinj 2 e)
    have h3pair : h 3 1 ≠ h 3 2 := fun e => (by decide : (1 : Fin 3) ≠ 2) (hinj 3 e)
    have hab : Fin.castAdd 2 (w 3) ≠ Fin.castAdd 2 (w 2) := fun e => hyd (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_inj e).symm
    have hmatch2 := equal_external_triple_forces_shared_exposed_color 5
      (Fin.castAdd 2 (w 3)) (Fin.castAdd 2 (w 2)) (h 2 0) (h 2 2) (h 3 1) (h 3 2)
      (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _)
      (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _) hab
      (h2forbid 0) (h2forbid 2) (h3forbid 1) (h3forbid 2) h2pair h3pair
    rcases hmatch2 with hm | hm | hm | hm
    · exact hint2.1 hm
    · exact hint2.2.1 hm
    · exact hint2.2.2.1 hm
    · exact hint2.2.2.2 hm
  have hx_cases := op874_tight_minority_disjoint_three_interface_obstruction_exhaust_four (w 5) (w 4) (w 0) (w 3) (w 1) hmatch hxc hxd
  have hy_cases := op874_tight_minority_disjoint_three_interface_obstruction_exhaust_four (w 5) (w 4) (w 0) (w 3) (w 2) hmatch hyc hyd
  have hab5 : Fin.castAdd 2 (w 5) ≠ Fin.castAdd 2 (w 4) := by
    intro e
    have eq := op874_tight_minority_disjoint_three_interface_obstruction_castAdd_inj e
    have h03 : (0 : Fin 4) = 3 := hmatch (by simpa using eq)
    exact (by decide : (0 : Fin 4) ≠ 3) h03
  have h5forbid (p : Fin 3) : h 5 p ≠ 5 ∧ h 5 p ≠ Fin.castAdd 2 (w 5) ∧ h 5 p ≠ Fin.castAdd 2 (w 4) := by
    have hp := hforbid 5 p
    rw [hbit5] at hp
    simp only [ite_true] at hp
    rw [hm5] at hp
    exact ⟨hp.1, hp.2.2, hp.2.1⟩
  have h2forbid_5 (p : Fin 3) : h 2 p ≠ 5 ∧ h 2 p ≠ Fin.castAdd 2 (w 5) ∧ h 2 p ≠ Fin.castAdd 2 (w 4) := by
    have hp := hforbid 2 p
    rw [hbit2] at hp
    simp only [ite_true] at hp
    rw [hm2] at hp
    rcases hx_cases with hx5 | hx4 <;> rcases hy_cases with hy5 | hy4
    · exfalso; apply hxy; rw [hx5, hy5]
    · rw [hx5, hy4] at hp
      exact hp
    · rw [hx4, hy5] at hp
      exact ⟨hp.1, hp.2.2, hp.2.1⟩
    · exfalso; apply hxy; rw [hx4, hy4]
  have h2pair : h 2 0 ≠ h 2 1 := fun e => (by decide : (0 : Fin 3) ≠ 1) (hinj 2 e)
  have h5pair : h 5 0 ≠ h 5 1 := fun e => (by decide : (0 : Fin 3) ≠ 1) (hinj 5 e)
  have hmatch_final := equal_external_triple_forces_shared_exposed_color 5
    (Fin.castAdd 2 (w 5)) (Fin.castAdd 2 (w 4)) (h 2 0) (h 2 1) (h 5 0) (h 5 1)
    (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _)
    (op874_tight_minority_disjoint_three_interface_obstruction_castAdd_ne_five _) hab5
    (h2forbid_5 0) (h2forbid_5 1) (h5forbid 0) (h5forbid 1) h2pair h5pair
  rcases hmatch_final with hm | hm | hm | hm
  · exact hmatching.1 hm
  · exact hmatching.2.1 hm
  · exact hmatching.2.2.1 hm
  · exact hmatching.2.2.2 hm
