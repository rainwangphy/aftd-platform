import AFTD.Prelude

/-!
# finite_linear_cover_omit_two_unforced_in_one_triple

Topic: graphs   Node: 9ff838ac1040

Provenance: helper lemma. Elementary linear-family exchange in the triangle packing-cover campaign.

Let the union U of a packing cover a linear set family. If two points x,y of the same three-element packed set are not the sole U-point of any family member, then removing x and y from U leaves a cover.
-/

theorem finite_linear_cover_omit_two_unforced_in_one_triple
    {α : Type*} [DecidableEq α] (F P : Finset (Finset α))
    (hsub : P ⊆ F)
    (hlinear : (F : Set (Finset α)).Pairwise (fun a b => (a ∩ b).card ≤ 1))
    (hcover : ∀ t ∈ F, ¬ Disjoint (P.biUnion id) t)
    (p : Finset α) (hp : p ∈ P) (hp3 : p.card = 3)
    (x y : α) (hx : x ∈ p) (hy : y ∈ p) (hne : x ≠ y)
    (hxunforced : ∀ t ∈ F, t ∩ P.biUnion id ≠ {x})
    (hyunforced : ∀ t ∈ F, t ∩ P.biUnion id ≠ {y}) :
    ∀ t ∈ F, ¬ Disjoint ((P.biUnion id) \ {x,y}) t := by
  intro t ht hdisj
  have hxU : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
  have hyU : y ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨p, hp, hy⟩
  obtain ⟨a, haU, hat⟩ := Finset.not_disjoint_iff.mp (hcover t ht)
  have haxy : a = x ∨ a = y := by
    by_contra h
    push_neg at h
    have ha : a ∈ (P.biUnion id) \ {x,y} := by
      rw [Finset.mem_sdiff]
      exact ⟨haU, by simp [h.1, h.2]⟩
    exact (Finset.disjoint_left.mp hdisj ha) hat
  have hxy_mem : x ∈ t ∨ y ∈ t := by
    rcases haxy with rfl | rfl
    · exact Or.inl hat
    · exact Or.inr hat
  have hnot_both : ¬ (x ∈ t ∧ y ∈ t) := by
    rintro ⟨hxt, hyt⟩
    by_cases htp : t = p
    · subst t
      have hsubxy : ({x,y} : Finset α) ⊆ p := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hcard_sdiff : (p \ {x,y}).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsubxy, hp3, Finset.card_pair hne]
      have hnonempty : (p \ {x,y}).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h] at hcard_sdiff
        simp at hcard_sdiff
      obtain ⟨z, hzmem⟩ := hnonempty
      rw [Finset.mem_sdiff] at hzmem
      obtain ⟨hzp, hzxy⟩ := hzmem
      have hzU : z ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨p, hp, hzp⟩
      have hz' : z ∈ (P.biUnion id) \ {x,y} := by
        rw [Finset.mem_sdiff]
        exact ⟨hzU, hzxy⟩
      exact (Finset.disjoint_left.mp hdisj hz') hzp
    · have hcard := hlinear ht (hsub hp) htp
      have hsubset : ({x,y} : Finset α) ⊆ t ∩ p := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hxt, hx⟩
        · exact Finset.mem_inter.mpr ⟨hyt, hy⟩
      have hcard2 : 2 ≤ (t ∩ p).card := by
        calc
          2 = ({x,y} : Finset α).card := (Finset.card_pair hne).symm
          _ ≤ (t ∩ p).card := Finset.card_le_card hsubset
      omega
  rcases hxy_mem with hxt | hyt
  · have hyt : y ∉ t := fun h => hnot_both ⟨hxt, h⟩
    have hInter : t ∩ (P.biUnion id) = {x} := by
      ext z
      constructor
      · intro hz
        rw [Finset.mem_inter] at hz
        obtain ⟨hzt, hzU⟩ := hz
        have hzxy : z = x ∨ z = y := by
          by_contra h
          push_neg at h
          have hz' : z ∈ (P.biUnion id) \ {x,y} := by
            rw [Finset.mem_sdiff]
            exact ⟨hzU, by simp [h.1, h.2]⟩
          exact (Finset.disjoint_left.mp hdisj hz') hzt
        rcases hzxy with rfl | rfl
        · simp
        · exact False.elim (hyt hzt)
      · intro hz
        rw [Finset.mem_singleton] at hz
        subst z
        exact Finset.mem_inter.mpr ⟨hxt, hxU⟩
    exact hxunforced t ht hInter
  · have hxt : x ∉ t := fun h => hnot_both ⟨h, hyt⟩
    have hInter : t ∩ (P.biUnion id) = {y} := by
      ext z
      constructor
      · intro hz
        rw [Finset.mem_inter] at hz
        obtain ⟨hzt, hzU⟩ := hz
        have hzxy : z = x ∨ z = y := by
          by_contra h
          push_neg at h
          have hz' : z ∈ (P.biUnion id) \ {x,y} := by
            rw [Finset.mem_sdiff]
            exact ⟨hzU, by simp [h.1, h.2]⟩
          exact (Finset.disjoint_left.mp hdisj hz') hzt
        rcases hzxy with rfl | rfl
        · exact False.elim (hxt hzt)
        · simp
      · intro hz
        rw [Finset.mem_singleton] at hz
        subst z
        exact Finset.mem_inter.mpr ⟨hyt, hyU⟩
    exact hyunforced t ht hInter
