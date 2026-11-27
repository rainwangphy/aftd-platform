import AFTD.Prelude

/-!
# op874_square_equal_color_forces_common_gap

Topic: graphs   Node: a0aeefad4ce6

Provenance: helper lemma. Equal-color four-port obstruction for OP-874 using the local-state criterion in arXiv:2610.41950; experiments 43551 and 43555.

Let the outside edges of a square all have the same external color a. At the four outside ports prescribe forbidden two-color sets disjoint from the exposed local hidden pairs, with opposite forbidden pairs disjoint and excluding a. If the square has compatible local states using all six colors at each vertex and disjoint exposed pairs on every square edge, then the unions of the opposite forbidden pairs are equal.
-/

private theorem in1276_square_logic
    {A B0 B1 B2 C0 C1 C2 D0 D1 D2 : Prop}
    (sb : B0 ∨ B1 ∨ B2) (sc : C0 ∨ C1 ∨ C2) (sd : D0 ∨ D1 ∨ D2)
    (ab0 : A → ¬ B0) (ab1 : A → ¬ B1)
    (_bc0 : B2 → ¬ C0) (bc1 : B2 → ¬ C1)
    (cd0 : C0 → ¬ D1) (cd2 : C2 → ¬ D1)
    (da0 : D0 → ¬ A) (da2 : D2 → ¬ A) : ¬ A := by
  intro ha
  have hb2 : B2 := by
    rcases sb with hb0 | hb1 | hb2
    · exact False.elim (ab0 ha hb0)
    · exact False.elim (ab1 ha hb1)
    · exact hb2
  have hd1 : D1 := by
    rcases sd with hd0 | hd1 | hd2
    · exact False.elim (da0 hd0 ha)
    · exact hd1
    · exact False.elim (da2 hd2 ha)
  rcases sc with hc0 | hc1 | hc2
  · exact cd0 hc0 hd1
  · exact bc1 hb2 hc1
  · exact cd2 hc2 hd1

theorem in1276_square_hidden_color_exposed_outside
    (p : Fin 4 → Fin 3 → Prop)
    (hsome : ∀ v, p v 0 ∨ p v 1 ∨ p v 2)
    (hcross : ∀ v, ¬ (p v 0 ∧ p (v+1) 0) ∧
      ¬ (p v 0 ∧ p (v+1) 1) ∧ ¬ (p v 2 ∧ p (v+1) 0) ∧
      ¬ (p v 2 ∧ p (v+1) 1)) :
    ∀ v, ¬ p v 0 := by
  intro v
  fin_cases v
  · have sb := hsome 1
    have sc := hsome 2
    have sd := hsome 3
    have ab := hcross 0
    have bc := hcross 1
    have cd := hcross 2
    have da := hcross 3
    norm_num at ab bc cd da
    exact in1276_square_logic sb sc sd ab.1 ab.2.1 bc.2.2.1 bc.2.2.2 cd.2.1 cd.2.2.2 da.1 da.2.2.1
  · have sb := hsome 2
    have sc := hsome 3
    have sd := hsome 0
    have ab := hcross 1
    have bc := hcross 2
    have cd := hcross 3
    have da := hcross 0
    norm_num at ab bc cd da
    exact in1276_square_logic sb sc sd ab.1 ab.2.1 bc.2.2.1 bc.2.2.2 cd.2.1 cd.2.2.2 da.1 da.2.2.1
  · have sb := hsome 3
    have sc := hsome 0
    have sd := hsome 1
    have ab := hcross 2
    have bc := hcross 3
    have cd := hcross 0
    have da := hcross 1
    norm_num at ab bc cd da
    exact in1276_square_logic sb sc sd ab.1 ab.2.1 bc.2.2.1 bc.2.2.2 cd.2.1 cd.2.2.2 da.1 da.2.2.1
  · have sb := hsome 0
    have sc := hsome 1
    have sd := hsome 2
    have ab := hcross 3
    have bc := hcross 0
    have cd := hcross 1
    have da := hcross 2
    norm_num at ab bc cd da
    exact in1276_square_logic sb sc sd ab.1 ab.2.1 bc.2.2.1 bc.2.2.2 cd.2.1 cd.2.2.2 da.1 da.2.2.1

theorem in1276_square_has_common_outside_exposed_color
    (a : Fin 6) (e : Fin 4 → Fin 6) (h : Fin 4 → Fin 3 → Fin 6)
    (hlocal : ∀ v, ({a,e v,e (v-1),h v 0,h v 1,h v 2} : Finset (Fin 6)).card = 6)
    (hcross : ∀ v, Disjoint ({h v 0,h v 2} : Finset (Fin 6))
      {h (v+1) 0,h (v+1) 1}) :
    ∃ q : Fin 6, q ≠ a ∧ ∀ v, q = h v 1 ∨ q = h v 2 := by
  let vals : Fin 5 → Fin 6 := ![a,e 0,e 1,e 2,e 3]
  let C : Finset (Fin 6) := Finset.univ.image vals
  have hC : C.card ≤ 5 := by
    simpa [C] using (Finset.card_image_le (s := Finset.univ) (f := vals))
  have hne : C ≠ Finset.univ := by
    intro he
    rw [he] at hC
    simp at hC
  have hex : ∃ q, q ∉ C := by
    by_contra hn
    push_neg at hn
    apply hne
    ext q
    simp [hn q]
  obtain ⟨q, hq⟩ := hex
  have hqv (i : Fin 5) : q ≠ vals i := by
    intro he
    apply hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩
  have hqa : q ≠ a := hqv 0
  have hqe (v : Fin 4) : q ≠ e v := by
    fin_cases v
    · exact hqv 1
    · exact hqv 2
    · exact hqv 3
    · exact hqv 4
  have hsome (v : Fin 4) : q = h v 0 ∨ q = h v 1 ∨ q = h v 2 := by
    let S : Finset (Fin 6) := {a,e v,e (v-1),h v 0,h v 1,h v 2}
    have hs : S = Finset.univ := Finset.eq_univ_of_card _ (hlocal v)
    have hm : q ∈ S := by rw [hs]; exact Finset.mem_univ _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with ha | he | hp | h0 | h1 | h2
    · exact False.elim (hqa ha)
    · exact False.elim (hqe v he)
    · exact False.elim (hqe (v-1) hp)
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  have hcx (v : Fin 4) :
      ¬ (q = h v 0 ∧ q = h (v+1) 0) ∧
      ¬ (q = h v 0 ∧ q = h (v+1) 1) ∧
      ¬ (q = h v 2 ∧ q = h (v+1) 0) ∧
      ¬ (q = h v 2 ∧ q = h (v+1) 1) := by
    have hd := Finset.disjoint_left.mp (hcross v)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hh; exact hd (Or.inl hh.1) (Or.inl hh.2)
    · intro hh; exact hd (Or.inl hh.1) (Or.inr hh.2)
    · intro hh; exact hd (Or.inr hh.1) (Or.inl hh.2)
    · intro hh; exact hd (Or.inr hh.1) (Or.inr hh.2)
  have hnot := in1276_square_hidden_color_exposed_outside (fun v j => q = h v j) hsome hcx
  refine ⟨q, hqa, ?_⟩
  intro v
  have hs := hsome v
  have hn := hnot v
  rcases hs with h0 | h1 | h2
  · exact False.elim (hn h0)
  · exact Or.inl h1
  · exact Or.inr h2

theorem op874_square_equal_color_forces_common_gap
    (a : Fin 6) (U : Fin 4 → Finset (Fin 6))
    (hsize : ∀ v, (U v).card = 2) (havoid : ∀ v, a ∉ U v)
    (hpair0 : Disjoint (U 0) (U 2)) (hpair1 : Disjoint (U 1) (U 3))
    (e : Fin 4 → Fin 6) (h : Fin 4 → Fin 3 → Fin 6)
    (hlocal : ∀ v, ({a,e v,e (v-1),h v 0,h v 1,h v 2} : Finset (Fin 6)).card = 6)
    (hcross : ∀ v, Disjoint ({h v 0,h v 2} : Finset (Fin 6)) {h (v+1) 0,h (v+1) 1})
    (houtside : ∀ v, Disjoint (U v) ({h v 1,h v 2} : Finset (Fin 6))) :
    U 0 ∪ U 2 = U 1 ∪ U 3 := by
  obtain ⟨q, hqa, hq⟩ := in1276_square_has_common_outside_exposed_color a e h hlocal hcross
  have hqU (v : Fin 4) : q ∉ U v := by
    intro hm
    have hd := Finset.disjoint_left.mp (houtside v)
    have hmem : q ∈ ({h v 1,h v 2} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hq v
    exact hd hm hmem
  let C : Finset (Fin 6) := (Finset.univ.erase a).erase q
  have hC : C.card = 4 := by
    simp [C, hqa, Ne.symm hqa]
  have subset (v w : Fin 4) : U v ∪ U w ⊆ C := by
    intro x hx
    simp only [Finset.mem_union] at hx
    simp only [C, Finset.mem_erase, Finset.mem_univ, and_true]
    rcases hx with hx | hx
    · exact ⟨fun he => hqU v (he ▸ hx), fun he => havoid v (he ▸ hx)⟩
    · exact ⟨fun he => hqU w (he ▸ hx), fun he => havoid w (he ▸ hx)⟩
  have hc0 : (U 0 ∪ U 2).card = C.card := by
    rw [Finset.card_union_of_disjoint hpair0, hsize 0, hsize 2, hC]
  have hc1 : (U 1 ∪ U 3).card = C.card := by
    rw [Finset.card_union_of_disjoint hpair1, hsize 1, hsize 3, hC]
  have he0 : U 0 ∪ U 2 = C := Finset.eq_of_subset_of_card_le (subset 0 2) (by omega)
  have he1 : U 1 ∪ U 3 = C := Finset.eq_of_subset_of_card_le (subset 1 3) (by omega)
  exact he0.trans he1.symm
