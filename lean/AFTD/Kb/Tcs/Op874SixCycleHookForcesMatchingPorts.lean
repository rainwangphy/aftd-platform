import AFTD.Prelude

/-!
# op874_six_cycle_hook_forces_matching_ports

Topic: combinatorics   Node: cd272a0bb791

Provenance: helper lemma. Palette steps for the six-cycle low-port obstruction in OP-874; https://arxiv.org/abs/2610.41950.

Compatibility at the 5–0 factor interface and the 1–5 matching interface, together with the two indicated low ports, forces three hidden matching/factor colors on the six-cycle.
-/

private theorem six_vec_inj (a b c d x y : Fin 6)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hax : a ≠ x) (hay : a ≠ y)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbx : b ≠ x) (hby : b ≠ y)
    (hcd : c ≠ d) (hcx : c ≠ x) (hcy : c ≠ y)
    (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y) :
    Function.Injective ![a,b,c,d,x,y] := by
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Fin.reduceEq] at he ⊢ <;> aesop

private theorem six_frame
    (a b c d x y z : Fin 6)
    (hi : Function.Injective ![a,b,c,d,x,y])
    (hz : z ≠ b ∧ z ≠ c ∧ z ≠ d ∧ z ≠ x ∧ z ≠ y) : z = a := by
  let q : Fin 6 → Fin 6 := ![a,b,c,d,x,y]
  have hcard : (Finset.univ.image q).card = Fintype.card (Fin 6) := by
    rw [Finset.card_image_iff.mpr (Set.injOn_of_injective hi)]
    simp
  have hall : Finset.univ.image q = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hm : z ∈ Finset.univ.image q := by rw [hall]; exact Finset.mem_univ _
  obtain ⟨i, _, hiq⟩ := Finset.mem_image.mp hm
  fin_cases i <;> simp_all [q]

private theorem high_ne_four (t : Fin 4) : Fin.castAdd 2 t ≠ (4 : Fin 6) := by
  fin_cases t <;> decide

private theorem high_ne_five (t : Fin 4) : Fin.castAdd 2 t ≠ (5 : Fin 6) := by
  fin_cases t <;> decide

private theorem high_inj {s t : Fin 4} (h : s ≠ t) :
    Fin.castAdd 2 s ≠ Fin.castAdd 2 t := by
  intro hh
  apply h
  apply Fin.ext
  simpa only [Fin.val_castAdd] using congrArg Fin.val hh

theorem op874_six_cycle_hook_forces_matching_ports
    (w : Fin 6 → Fin 4) (h : Fin 6 → Fin 3 → Fin 6)
    (hproper : ∀ i, w (i-1) ≠ w i)
    (hinj : ∀ i, Function.Injective (h i))
    (havoid : ∀ i p,
      h i p ≠ (if (![false,true,true,false,true,true] : Fin 6 → Bool) i then 5 else 4) ∧
      h i p ≠ Fin.castAdd 2 (w (i-1)) ∧ h i p ≠ Fin.castAdd 2 (w i))
    (hcycle : h 5 0 ≠ h 0 1 ∧ h 5 0 ≠ h 0 2 ∧
      h 5 2 ≠ h 0 1 ∧ h 5 2 ≠ h 0 2)
    (hmatch : h 1 0 ≠ h 5 0 ∧ h 1 0 ≠ h 5 1 ∧
      h 1 1 ≠ h 5 0 ∧ h 1 1 ≠ h 5 1)
    (hfixed0 : h 0 0 = 5) (hfixed5 : h 5 0 = 4) :
    h 5 2 = Fin.castAdd 2 (w 0) ∧ h 1 2 = 4 ∧
      h 5 1 = Fin.castAdd 2 (w 1) := by
  let a : Fin 6 := Fin.castAdd 2 (w 0)
  let b : Fin 6 := Fin.castAdd 2 (w 1)
  let f : Fin 6 := Fin.castAdd 2 (w 5)
  have hm6 : (-1 : Fin 6) = 5 := by decide
  have haf : a ≠ f := by
    apply high_inj
    have hp := hproper 0
    simpa [hm6] using hp.symm
  have hab : a ≠ b := by
    apply high_inj
    simpa using hproper 1
  have ha4 : a ≠ 4 := high_ne_four _
  have ha5 : a ≠ 5 := high_ne_five _
  have hb4 : b ≠ 4 := high_ne_four _
  have hb5 : b ≠ 5 := high_ne_five _
  have hf4 : f ≠ 4 := high_ne_four _
  have hf5 : f ≠ 5 := high_ne_five _
  have hx := havoid 0 1
  have hy := havoid 0 2
  have hz := havoid 5 2
  have hxy : h 0 1 ≠ h 0 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (hinj 0 he)
  have hx5 : h 0 1 ≠ 5 := by
    intro he
    exact (by decide : (1 : Fin 3) ≠ 0) (hinj 0 (he.trans hfixed0.symm))
  have hy5 : h 0 2 ≠ 5 := by
    intro he
    exact (by decide : (2 : Fin 3) ≠ 0) (hinj 0 (he.trans hfixed0.symm))
  have hz4 : h 5 2 ≠ 4 := by
    intro he
    exact (by decide : (2 : Fin 3) ≠ 0) (hinj 5 (he.trans hfixed5.symm))
  have hx4 : h 0 1 ≠ 4 := by simpa using hx.1
  have hy4 : h 0 2 ≠ 4 := by simpa using hy.1
  have hxf : h 0 1 ≠ f := by simpa [f,hm6] using hx.2.1
  have hyf : h 0 2 ≠ f := by simpa [f,hm6] using hy.2.1
  have hxa : h 0 1 ≠ a := by simpa [a] using hx.2.2
  have hya : h 0 2 ≠ a := by simpa [a] using hy.2.2
  have h5a : h 5 2 = a := by
    apply six_frame a f 4 5 (h 0 1) (h 0 2) (h 5 2)
    · exact six_vec_inj a f 4 5 (h 0 1) (h 0 2)
        haf ha4 ha5 hxa.symm hya.symm hf4 hf5 hxf.symm hyf.symm
        (by decide) hx4.symm hy4.symm hx5.symm hy5.symm hxy
    · refine ⟨?_, hz4, ?_, hcycle.2.2.1, hcycle.2.2.2⟩
      · simpa [f] using hz.2.2
      · simpa using hz.1
  have h10 := havoid 1 0
  have h11 := havoid 1 1
  have h12 := havoid 1 2
  have h104 : h 1 0 ≠ 4 := by simpa [hfixed5] using hmatch.1
  have h114 : h 1 1 ≠ 4 := by simpa [hfixed5] using hmatch.2.2.1
  have h1011 : h 1 0 ≠ h 1 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj 1 he)
  have h12x : h 1 2 ≠ h 1 0 := fun he => (by decide : (2 : Fin 3) ≠ 0) (hinj 1 he)
  have h12y : h 1 2 ≠ h 1 1 := fun he => (by decide : (2 : Fin 3) ≠ 1) (hinj 1 he)
  have h105 : h 1 0 ≠ 5 := by simpa using h10.1
  have h115 : h 1 1 ≠ 5 := by simpa using h11.1
  have h10a : h 1 0 ≠ a := by simpa [a] using h10.2.1
  have h11a : h 1 1 ≠ a := by simpa [a] using h11.2.1
  have h10b : h 1 0 ≠ b := by simpa [b] using h10.2.2
  have h11b : h 1 1 ≠ b := by simpa [b] using h11.2.2
  have h14 : h 1 2 = 4 := by
    apply six_frame 4 5 a b (h 1 0) (h 1 1) (h 1 2)
    · exact six_vec_inj 4 5 a b (h 1 0) (h 1 1)
        (by decide) ha4.symm hb4.symm h104.symm h114.symm ha5.symm hb5.symm
        h105.symm h115.symm hab h10a.symm h11a.symm h10b.symm h11b.symm h1011
    · refine ⟨?_, ?_, ?_, h12x, h12y⟩
      · simpa using h12.1
      · simpa [a] using h12.2.1
      · simpa [b] using h12.2.2
  have h51 := havoid 5 1
  have h51a : h 5 1 ≠ a := by
    intro he
    exact (by decide : (1 : Fin 3) ≠ 2) (hinj 5 (he.trans h5a.symm))
  have h514 : h 5 1 ≠ 4 := by
    intro he
    exact (by decide : (1 : Fin 3) ≠ 0) (hinj 5 (he.trans hfixed5.symm))
  have h5b : h 5 1 = b := by
    apply six_frame b a 4 5 (h 1 0) (h 1 1) (h 5 1)
    · exact six_vec_inj b a 4 5 (h 1 0) (h 1 1)
        hab.symm hb4 hb5 h10b.symm h11b.symm ha4 ha5 h10a.symm h11a.symm
        (by decide) h104.symm h114.symm h105.symm h115.symm h1011
    · refine ⟨h51a, h514, ?_, hmatch.2.1.symm, hmatch.2.2.2.symm⟩
      simpa using h51.1
  exact ⟨by simpa [a] using h5a, h14, by simpa [b] using h5b⟩
