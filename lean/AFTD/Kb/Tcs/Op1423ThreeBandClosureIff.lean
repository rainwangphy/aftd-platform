import AFTD.Prelude

/-!
# op_1423_three_band_closure_iff

Topic: combinatorics   Node: 4a65c49ed328

Provenance: helper lemma. Structural closure step for op_1423_two_band_binomial_count, following the band decomposition in OP-1423.

For 1 ≤ m, 3m ≤ F < 4m and finite sets A ⊆ [m,2m), B ⊆ [2m,3m), C ⊆ [3m,F), the union A ∪ B ∪ C is closed under sums at most F if and only if F is in neither A+A nor A+B, every element of (A+A) in [2m,3m) is in B, and every element of ((A+A) ∪ (A+B)) in [3m,F) is in C.
-/

theorem op_1423_three_band_closure_iff (F m : ℕ) (hm : 1 ≤ m) (hlow : 3*m ≤ F) (hhigh : F < 4*m)
    (A B C : Finset ℕ)
    (hA : A ⊆ Finset.Ico m (2*m))
    (hB : B ⊆ Finset.Ico (2*m) (3*m))
    (hC : C ⊆ Finset.Ico (3*m) F) :
    (∀ x ∈ A ∪ B ∪ C, ∀ y ∈ A ∪ B ∪ C, x+y ≤ F → x+y ∈ A ∪ B ∪ C) ↔
    let AA := Finset.image₂ (fun a b : ℕ => a+b) A A
    let AB := Finset.image₂ (fun a b : ℕ => a+b) A B
    let P := (AA ∪ AB).filter (fun x => 3*m ≤ x ∧ x < F)
    F ∉ AA ∧ F ∉ AB ∧ AA ∩ Finset.Ico (2*m) (3*m) ⊆ B ∧ P ⊆ C := by
  have a_bounds : ∀ x ∈ A, m ≤ x ∧ x < 2*m := by
    intro x hx; exact Finset.mem_Ico.mp (hA hx)
  have b_bounds : ∀ x ∈ B, 2*m ≤ x ∧ x < 3*m := by
    intro x hx; exact Finset.mem_Ico.mp (hB hx)
  have c_bounds : ∀ x ∈ C, 3*m ≤ x ∧ x < F := by
    intro x hx; exact Finset.mem_Ico.mp (hC hx)
  have xin : ∀ x, x ∈ A ∪ B ∪ C → m ≤ x ∧ x < F := by
    intro x hx
    simp only [Finset.mem_union] at hx
    rcases hx with (ha | hb) | hc
    · have := a_bounds x ha; omega
    · have := b_bounds x hb; omega
    · have := c_bounds x hc; omega
  simp only
  constructor
  · intro h
    have hnof : F ∉ A ∪ B ∪ C := by
      intro hf
      have := xin F hf
      omega
    have hnoaa : F ∉ Finset.image₂ (fun a b : ℕ => a+b) A A := by
      intro hf
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_image₂.mp hf
      have hh := h a (by simp [ha]) b (by simp [hb]) (by omega)
      apply hnof
      simpa only [hab] using hh
    have hnoab : F ∉ Finset.image₂ (fun a b : ℕ => a+b) A B := by
      intro hf
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_image₂.mp hf
      have hh := h a (by simp [ha]) b (by simp [hb]) (by omega)
      apply hnof
      simpa only [hab] using hh
    refine ⟨hnoaa,hnoab,?_,?_⟩
    · intro z hz
      obtain ⟨haa,hband⟩ := Finset.mem_inter.mp hz
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_image₂.mp haa
      have hband' := Finset.mem_Ico.mp hband
      have hz' : z ∈ A ∪ B ∪ C := by
        have hh := h a (by simp [ha]) b (by simp [hb]) (by omega)
        simpa only [hab] using hh
      simp only [Finset.mem_union] at hz'
      rcases hz' with (ha' | hb') | hc'
      · have := a_bounds z ha'; omega
      · exact hb'
      · have := c_bounds z hc'; omega
    · intro z hz
      obtain ⟨hs,hrange⟩ := Finset.mem_filter.mp hz
      obtain ⟨hlo,hhi⟩ := hrange
      have hz' : z ∈ A ∪ B ∪ C := by
        rcases Finset.mem_union.mp hs with haa | hab
        · obtain ⟨a,ha,b,hb,heq⟩ := Finset.mem_image₂.mp haa
          have hh := h a (by simp [ha]) b (by simp [hb]) (by omega)
          simpa only [heq] using hh
        · obtain ⟨a,ha,b,hb,heq⟩ := Finset.mem_image₂.mp hab
          have hh := h a (by simp [ha]) b (by simp [hb]) (by omega)
          simpa only [heq] using hh
      simp only [Finset.mem_union] at hz'
      rcases hz' with (ha' | hb') | hc'
      · have := a_bounds z ha'; omega
      · have := b_bounds z hb'; omega
      · exact hc'
  · rintro ⟨hnoaa,hnoab,hforce,hP⟩ x hx y hy hxy
    simp only [Finset.mem_union] at hx hy ⊢
    rcases hx with (ha | hb) | hc <;> rcases hy with (ha' | hb') | hc'
    · have hax := a_bounds x ha
      have hay := a_bounds y ha'
      have hsum : x+y ∈ Finset.image₂ (fun a b : ℕ => a+b) A A := Finset.mem_image₂.mpr ⟨x,ha,y,ha',rfl⟩
      have hne : x+y ≠ F := by
        intro heq
        exact hnoaa (by simpa only [heq] using hsum)
      have hlt : x+y < F := by omega
      by_cases hband : x+y < 3*m
      · left; right
        apply hforce
        exact Finset.mem_inter.mpr ⟨hsum, Finset.mem_Ico.mpr (by omega)⟩
      · right
        apply hP
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union.mpr (Or.inl hsum), by omega⟩
    · have hax := a_bounds x ha
      have hby := b_bounds y hb'
      have hsum : x+y ∈ Finset.image₂ (fun a b : ℕ => a+b) A B := Finset.mem_image₂.mpr ⟨x,ha,y,hb',rfl⟩
      have hne : x+y ≠ F := by
        intro heq
        exact hnoab (by simpa only [heq] using hsum)
      have hlt : x+y < F := by omega
      right; apply hP; apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union.mpr (Or.inr hsum), by omega⟩
    · have := a_bounds x ha; have := c_bounds y hc'; omega
    · have hbx := b_bounds x hb
      have hay := a_bounds y ha'
      have hsum : x+y ∈ Finset.image₂ (fun a b : ℕ => a+b) A B := by
        have h : y+x ∈ Finset.image₂ (fun a b : ℕ => a+b) A B := Finset.mem_image₂.mpr ⟨y,ha',x,hb,rfl⟩
        simpa only [Nat.add_comm] using h
      have hne : x+y ≠ F := by
        intro heq
        exact hnoab (by simpa only [heq] using hsum)
      have hlt : x+y < F := by omega
      right; apply hP; apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_union.mpr (Or.inr hsum), by omega⟩
    · have := b_bounds x hb; have := b_bounds y hb'; omega
    · have := b_bounds x hb; have := c_bounds y hc'; omega
    · have := c_bounds x hc; have := a_bounds y ha'; omega
    · have := c_bounds x hc; have := b_bounds y hb'; omega
    · have := c_bounds x hc; have := c_bounds y hc'; omega
