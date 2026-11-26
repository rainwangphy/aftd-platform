import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ContractionForcesEqualFactorPalette

/-!
# op874_six_cycle_next_block_forces_repeat

Topic: combinatorics   Node: 9d0ed2a19852

Provenance: helper lemma. Palette steps for the six-cycle low-port obstruction in OP-874; https://arxiv.org/abs/2610.41950.

The next two interfaces in the six-cycle kernel force the third high factor color to repeat the first when the four named high colors are distinct.
-/

private theorem nxt_six_vec_inj (a b c d x y : Fin 6)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hax : a ≠ x) (hay : a ≠ y)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbx : b ≠ x) (hby : b ≠ y)
    (hcd : c ≠ d) (hcx : c ≠ x) (hcy : c ≠ y)
    (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y) :
    Function.Injective ![a,b,c,d,x,y] := by
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Fin.reduceEq] at he ⊢ <;> aesop

private theorem nxt_six_frame
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

private theorem nxt_high_ne_four (t : Fin 4) : Fin.castAdd 2 t ≠ (4 : Fin 6) := by
  fin_cases t <;> decide

private theorem nxt_high_ne_five (t : Fin 4) : Fin.castAdd 2 t ≠ (5 : Fin 6) := by
  fin_cases t <;> decide

private theorem nxt_high_inj {s t : Fin 4} (h : s ≠ t) :
    Fin.castAdd 2 s ≠ Fin.castAdd 2 t := by
  intro hh
  apply h
  apply Fin.ext
  simpa only [Fin.val_castAdd] using congrArg Fin.val hh


private theorem nxt_four_highs_clash (t x y u v : Fin 6)
    (ht4 : t ≠ 4) (ht5 : t ≠ 5)
    (hx : x ≠ 4 ∧ x ≠ 5 ∧ x ≠ t)
    (hy : y ≠ 4 ∧ y ≠ 5 ∧ y ≠ t)
    (hu : u ≠ 4 ∧ u ≠ 5 ∧ u ≠ t)
    (hv : v ≠ 4 ∧ v ≠ 5 ∧ v ≠ t)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v) (huv : u ≠ v) : False := by
  have hi := nxt_six_vec_inj 4 5 t x y u (by decide) ht4.symm
    hx.1.symm hy.1.symm hu.1.symm ht5.symm hx.2.1.symm hy.2.1.symm
    hu.2.1.symm hx.2.2.symm hy.2.2.symm hu.2.2.symm hxy hxu hyu
  have he := nxt_six_frame 4 5 t x y u v hi
    ⟨hv.2.1, hv.2.2, hxv.symm, hyv.symm, huv.symm⟩
  exact hv.1 he

theorem op874_six_cycle_next_block_forces_repeat
    (a b c d e f : Fin 4) (h3 h4 : Fin 3 → Fin 6)
    (hfour : Function.Injective ![a,b,e,f]) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e)
    (h3inj : Function.Injective h3) (h4inj : Function.Injective h4)
    (h3avoid : ∀ p, h3 p ≠ 4 ∧ h3 p ≠ Fin.castAdd 2 c ∧ h3 p ≠ Fin.castAdd 2 d)
    (h4avoid : ∀ p, h4 p ≠ 5 ∧ h4 p ≠ Fin.castAdd 2 d ∧ h4 p ≠ Fin.castAdd 2 e)
    (h3low : h3 1 = 5)
    (h34 : h3 0 ≠ h4 1 ∧ h3 0 ≠ h4 2 ∧ h3 2 ≠ h4 1 ∧ h3 2 ≠ h4 2)
    (h45 : h4 0 ≠ Fin.castAdd 2 a ∧ h4 0 ≠ Fin.castAdd 2 b ∧
      h4 2 ≠ Fin.castAdd 2 a ∧ h4 2 ≠ Fin.castAdd 2 b) : c = a := by
  let A : Fin 6 := Fin.castAdd 2 a
  let B : Fin 6 := Fin.castAdd 2 b
  let C : Fin 6 := Fin.castAdd 2 c
  let D : Fin 6 := Fin.castAdd 2 d
  let E : Fin 6 := Fin.castAdd 2 e
  let F : Fin 6 := Fin.castAdd 2 f
  have hab : a ≠ b := by
    intro he; exact (by decide : (0 : Fin 4) ≠ 1) (hfour (by simpa using he))
  have hae : a ≠ e := by
    intro he; exact (by decide : (0 : Fin 4) ≠ 2) (hfour (by simpa using he))
  have haf : a ≠ f := by
    intro he; exact (by decide : (0 : Fin 4) ≠ 3) (hfour (by simpa using he))
  have hbe : b ≠ e := by
    intro he; exact (by decide : (1 : Fin 4) ≠ 2) (hfour (by simpa using he))
  have hbf : b ≠ f := by
    intro he; exact (by decide : (1 : Fin 4) ≠ 3) (hfour (by simpa using he))
  have hef : e ≠ f := by
    intro he; exact (by decide : (2 : Fin 4) ≠ 3) (hfour (by simpa using he))
  have h30 : h3 0 ≠ 4 ∧ h3 0 ≠ 5 ∧ h3 0 ≠ D := by
    refine ⟨(h3avoid 0).1, ?_, (h3avoid 0).2.2⟩
    intro he; exact (by decide : (0 : Fin 3) ≠ 1) (h3inj (he.trans h3low.symm))
  have h32 : h3 2 ≠ 4 ∧ h3 2 ≠ 5 ∧ h3 2 ≠ D := by
    refine ⟨(h3avoid 2).1, ?_, (h3avoid 2).2.2⟩
    intro he; exact (by decide : (2 : Fin 3) ≠ 1) (h3inj (he.trans h3low.symm))
  have h30c : h3 0 ≠ C := (h3avoid 0).2.1
  have h32c : h3 2 ≠ C := (h3avoid 2).2.1
  have h3032 : h3 0 ≠ h3 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (h3inj he)
  have h4042 : h4 0 ≠ h4 2 := fun he => (by decide : (0 : Fin 3) ≠ 2) (h4inj he)
  have h4142 : h4 1 ≠ h4 2 := fun he => (by decide : (1 : Fin 3) ≠ 2) (h4inj he)
  have h4041 : h4 0 ≠ h4 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (h4inj he)
  have h40not4 : h4 0 ≠ 4 := by
    intro he
    have h41 : h4 1 ≠ 4 ∧ h4 1 ≠ 5 ∧ h4 1 ≠ D := by
      refine ⟨?_, (h4avoid 1).1, (h4avoid 1).2.1⟩
      intro hh; exact h4041 (he.trans hh.symm)
    have h42 : h4 2 ≠ 4 ∧ h4 2 ≠ 5 ∧ h4 2 ≠ D := by
      refine ⟨?_, (h4avoid 2).1, (h4avoid 2).2.1⟩
      intro hh; exact h4042 (he.trans hh.symm)
    exact nxt_four_highs_clash D (h3 0) (h3 2) (h4 1) (h4 2)
      (nxt_high_ne_four d) (nxt_high_ne_five d) h30 h32 h41 h42 h3032
      h34.1 h34.2.1 h34.2.2.1 h34.2.2.2 h4142
  have h41not4 : h4 1 ≠ 4 := by
    intro he
    have h40 : h4 0 ≠ 4 ∧ h4 0 ≠ 5 ∧ h4 0 ≠ E :=
      ⟨h40not4, (h4avoid 0).1, (h4avoid 0).2.2⟩
    have h42 : h4 2 ≠ 4 ∧ h4 2 ≠ 5 ∧ h4 2 ≠ E := by
      refine ⟨?_, (h4avoid 2).1, (h4avoid 2).2.2⟩
      intro hh; exact h4142 (he.trans hh.symm)
    have ha : A ≠ 4 ∧ A ≠ 5 ∧ A ≠ E :=
      ⟨nxt_high_ne_four a, nxt_high_ne_five a, nxt_high_inj hae⟩
    have hb : B ≠ 4 ∧ B ≠ 5 ∧ B ≠ E :=
      ⟨nxt_high_ne_four b, nxt_high_ne_five b, nxt_high_inj hbe⟩
    exact nxt_four_highs_clash E A B (h4 0) (h4 2)
      (nxt_high_ne_four e) (nxt_high_ne_five e) ha hb h40 h42 (nxt_high_inj hab)
      h45.1.symm h45.2.2.1.symm h45.2.1.symm h45.2.2.2.symm h4042
  have h42low : h4 2 = 4 := by
    apply nxt_six_frame 4 5 D E (h4 0) (h4 1) (h4 2)
    · exact nxt_six_vec_inj 4 5 D E (h4 0) (h4 1) (by decide)
        (nxt_high_ne_four d).symm (nxt_high_ne_four e).symm h40not4.symm h41not4.symm
        (nxt_high_ne_five d).symm (nxt_high_ne_five e).symm (h4avoid 0).1.symm
        (h4avoid 1).1.symm (nxt_high_inj hde) (h4avoid 0).2.1.symm
        (h4avoid 1).2.1.symm (h4avoid 0).2.2.symm (h4avoid 1).2.2.symm h4041
    · exact ⟨(h4avoid 2).1, (h4avoid 2).2.1, (h4avoid 2).2.2,
        h4042.symm, h4142.symm⟩
  have h40f : h4 0 = F := by
    apply nxt_six_frame F A B E 4 5 (h4 0)
    · exact nxt_six_vec_inj F A B E 4 5 (nxt_high_inj haf.symm) (nxt_high_inj hbf.symm)
        (nxt_high_inj hef.symm) (nxt_high_ne_four f) (nxt_high_ne_five f) (nxt_high_inj hab)
        (nxt_high_inj hae) (nxt_high_ne_four a) (nxt_high_ne_five a) (nxt_high_inj hbe)
        (nxt_high_ne_four b) (nxt_high_ne_five b) (nxt_high_ne_four e) (nxt_high_ne_five e) (by decide)
    · exact ⟨h45.1, h45.2.1, (h4avoid 0).2.2, h40not4, (h4avoid 0).1⟩
  have h41c : h4 1 = C := by
    apply nxt_six_frame C D 4 5 (h3 0) (h3 2) (h4 1)
    · exact nxt_six_vec_inj C D 4 5 (h3 0) (h3 2) (nxt_high_inj hcd)
        (nxt_high_ne_four c) (nxt_high_ne_five c) h30c.symm h32c.symm
        (nxt_high_ne_four d) (nxt_high_ne_five d) h30.2.2.symm h32.2.2.symm
        (by decide) h30.1.symm h32.1.symm h30.2.1.symm h32.2.1.symm h3032
    · exact ⟨(h4avoid 1).2.1, h41not4, (h4avoid 1).1, h34.1.symm, h34.2.2.1.symm⟩
  have hce : c ≠ e := by
    intro he
    apply (h4avoid 1).2.2
    simpa [C, E, he] using h41c
  have hcf : c ≠ f := by
    intro he
    apply h4041
    calc
      h4 0 = F := h40f
      _ = C := by simp [C, F, he]
      _ = h4 1 := h41c.symm
  exact op874_contraction_forces_equal_factor_palette b a e f c hab.symm hbe hbf
    hae haf hef hbc.symm hce hcf
