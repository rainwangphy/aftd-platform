import AFTD.Prelude

/-!
# mdfrbf_colour_inj

Topic: combinatorics   Node: 79baa6c4f78a

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

There is a bijection from Fin (a + (b-1)) onto the colours of Fin (a+b) other than the fan colour Fin.natAdd a c, which fixes the a diamond colours (Fin.castAdd (b-1) col ↦ Fin.castAdd b col), sends fan colours to fan colours, and never takes the value Fin.natAdd a c.
-/

/-- Colour bijection from the a+b-1 colours surviving deletion of the fan colour c into the a+b colours, fixing the a diamond colours. -/
theorem mdfrbf_colour_inj (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (c : Fin b) :
    ∃ f : Fin (a + (b - 1)) → Fin (a + b),
      Function.Injective f ∧
      (∀ v : Fin (a + b), v ≠ Fin.natAdd a c → ∃ u : Fin (a + (b - 1)), f u = v) ∧
      (∀ col : Fin a, f (Fin.castAdd (b - 1) col) = Fin.castAdd b col) ∧
      (∀ u : Fin (b - 1), ∃ col' : Fin b, f (Fin.natAdd a u) = Fin.natAdd a col') ∧
      (∀ u : Fin (a + (b - 1)), f u ≠ Fin.natAdd a c) := by
  let g : Fin (b - 1) → Fin b := fun u =>
    if h : u.val < c.val then ⟨u.val, by omega⟩ else ⟨u.val + 1, by have := u.isLt; omega⟩
  let f : Fin (a + (b - 1)) → Fin (a + b) := fun v =>
    if h : v.val < a then ⟨v.val, by omega⟩
    else Fin.natAdd a (g ⟨v.val - a, by have := v.isLt; omega⟩)
  have g_inj : Function.Injective g := by
    intro u u' h
    apply Fin.ext
    dsimp [g] at h
    split_ifs at h with h1 h2 h1 h2
    all_goals simp only [Fin.mk.injEq] at h ⊢
    all_goals omega
  have g_ne : ∀ u : Fin (b - 1), (g u).val ≠ c.val := by
    intro u
    have g_val : (g u).val = if u.val < c.val then u.val else u.val + 1 := by
      dsimp [g]
      split_ifs <;> rfl
    rw [g_val]
    split_ifs with h
    · omega
    · omega
  have g_surj : ∀ w : Fin b, w.val ≠ c.val → ∃ u : Fin (b - 1), g u = w := by
    intro w hw
    by_cases hwlt : w.val < c.val
    · refine ⟨⟨w.val, by omega⟩, ?_⟩
      dsimp [g]
      rw [if_pos hwlt]
    · have hle : c.val < w.val := by omega
      refine ⟨⟨w.val - 1, by have := w.isLt; omega⟩, ?_⟩
      dsimp [g]
      have hnot : ¬ w.val - 1 < c.val := by omega
      rw [dif_neg hnot]
      apply Fin.ext
      simp
      omega
  have f_natAdd : ∀ u : Fin (b - 1), f (Fin.natAdd a u) = Fin.natAdd a (g u) := by
    intro u
    dsimp [f]
    rw [dif_neg (by omega)]
    congr 1
    congr 1
    apply Fin.ext
    simp
  have f_inj : Function.Injective f := by
    intro v v' h
    by_cases hv : v.val < a
    · by_cases hv' : v'.val < a
      · apply Fin.ext
        dsimp [f] at h
        rw [dif_pos hv, dif_pos hv'] at h
        have hval := congrArg (fun x : Fin (a + b) => x.val) h
        simpa using hval
      · dsimp [f] at h
        rw [dif_pos hv, dif_neg hv'] at h
        have hval := congrArg (fun x : Fin (a + b) => x.val) h
        rw [Fin.val_natAdd] at hval
        have hval' : v.val = a + (g ⟨v'.val - a, by have := v'.isLt; omega⟩).val := by
          simpa using hval
        omega
    · by_cases hv' : v'.val < a
      · dsimp [f] at h
        rw [dif_neg hv, dif_pos hv'] at h
        have hval := congrArg (fun x : Fin (a + b) => x.val) h
        rw [Fin.val_natAdd] at hval
        have hval' : a + (g ⟨v.val - a, by have := v.isLt; omega⟩).val = v'.val := by
          simpa using hval
        omega
      · dsimp [f] at h
        rw [dif_neg hv, dif_neg hv'] at h
        have hg : g ⟨v.val - a, by have := v.isLt; omega⟩ =
            g ⟨v'.val - a, by have := v'.isLt; omega⟩ := by
          apply Fin.ext
          have hval := congrArg (fun x : Fin (a + b) => x.val) h
          rw [Fin.val_natAdd, Fin.val_natAdd] at hval
          omega
        have hsub : v.val - a = v'.val - a :=
          congrArg (fun x : Fin (b - 1) => x.val) (g_inj hg)
        apply Fin.ext
        omega
  have f_cast : ∀ col : Fin a, f (Fin.castAdd (b - 1) col) = Fin.castAdd b col := by
    intro col
    dsimp [f]
    have h : col.val < a := col.isLt
    rw [dif_pos h]
    apply Fin.ext
    simpa using (Fin.val_castAdd b col).symm
  have f_fan : ∀ u : Fin (b - 1), ∃ col' : Fin b, f (Fin.natAdd a u) = Fin.natAdd a col' := by
    intro u
    exact ⟨g u, f_natAdd u⟩
  have f_ne : ∀ u : Fin (a + (b - 1)), f u ≠ Fin.natAdd a c := by
    intro u h
    by_cases hu : u.val < a
    · dsimp [f] at h
      rw [dif_pos hu] at h
      have hval := congrArg (fun x : Fin (a + b) => x.val) h
      rw [Fin.val_natAdd] at hval
      have hval' : u.val = a + c.val := by
        simpa using hval
      omega
    · let u0 : Fin (b - 1) := ⟨u.val - a, by have := u.isLt; omega⟩
      have hu_eq : u = Fin.natAdd a u0 := by
        apply Fin.ext
        simp [u0]
        omega
      rw [hu_eq, f_natAdd] at h
      have hval := congrArg (fun x : Fin (a + b) => x.val) h
      rw [Fin.val_natAdd, Fin.val_natAdd] at hval
      exact g_ne u0 (by omega)
  refine ⟨f, f_inj, ?_, f_cast, f_fan, f_ne⟩
  intro v hv
  by_cases hvlt : v.val < a
  · refine ⟨⟨v.val, by have := v.isLt; omega⟩, ?_⟩
    dsimp [f]
    rw [dif_pos hvlt]
  · have hvge : a ≤ v.val := by omega
    let w : Fin b := ⟨v.val - a, by have := v.isLt; omega⟩
    have hw_ne : w.val ≠ c.val := by
      intro hw
      apply hv
      apply Fin.ext
      rw [Fin.val_natAdd]
      dsimp [w] at hw
      omega
    obtain ⟨u0, hu0⟩ := g_surj w hw_ne
    refine ⟨Fin.natAdd a u0, ?_⟩
    rw [f_natAdd, hu0]
    apply Fin.ext
    rw [Fin.val_natAdd]
    dsimp [w]
    omega
