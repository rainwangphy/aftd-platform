import AFTD.Prelude

/-!
# exists_triangle_through_three_points_avoiding

Topic: combinatorics   Node: 7a16332e01fa

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover_of_le_three

For three pairwise distinct points A, B, C in ℝ² and any finite family F of segments, there is a (possibly degenerate) triangle whose three open sides contain A, B, C respectively and none of whose three sides belongs to F.
-/

open scoped Sym2

/-- A pair produced by an injective first coordinate has finite fibers as an unordered pair. -/
lemma exists_triangle_through_three_points_avoiding_finite_preimage_sym2
    (f g : ℝ → ℝ × ℝ) (hf : Function.Injective f) (e : Sym2 (ℝ × ℝ)) :
    {α | s(f α, g α) = e}.Finite := by
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e
  have hsub : {α | s(f α, g α) = e} ⊆ {α | f α = u} ∪ {α | f α = v} := by
    intro α hα
    have h1 : s(f α, g α) = s(u, v) := hα.trans huv.symm
    rcases Sym2.eq_iff.mp h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact Or.inl h2
    · exact Or.inr h2
  apply Set.Finite.subset _ hsub
  apply Set.Finite.union
  · have : {α | f α = u}.Subsingleton := fun a ha b hb => hf (ha.trans hb.symm)
    exact this.finite
  · have : {α | f α = v}.Subsingleton := fun a ha b hb => hf (ha.trans hb.symm)
    exact this.finite

/-- Preimage of a finite family of unordered pairs under an injective-first-coordinate map is finite. -/
lemma exists_triangle_through_three_points_avoiding_finite_preimage_finset_sym2
    (f g : ℝ → ℝ × ℝ) (hf : Function.Injective f) (F : Finset (Sym2 (ℝ × ℝ))) :
    {α | s(f α, g α) ∈ F}.Finite := by
  have h : {α | s(f α, g α) ∈ F} = ⋃ e ∈ (F : Set (Sym2 (ℝ×ℝ))), {α | s(f α, g α) = e} := by
    ext α; simp
  rw [h]
  apply Set.Finite.biUnion F.finite_toSet
  intro e _
  exact exists_triangle_through_three_points_avoiding_finite_preimage_sym2 f g hf e

/-- There is a triangle with A, B, C on its open sides whose three sides all avoid a given finite segment family. -/
theorem exists_triangle_through_three_points_avoiding
    (A B C : ℝ × ℝ) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (F : Finset (Sym2 (ℝ × ℝ))) :
    ∃ p₁ p₂ p₃ : ℝ × ℝ, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₃ ≠ p₁ ∧
      A ∈ openSegment ℝ p₁ p₂ ∧ B ∈ openSegment ℝ p₂ p₃ ∧ C ∈ openSegment ℝ p₃ p₁ ∧
      s(p₁, p₂) ∉ F ∧ s(p₂, p₃) ∉ F ∧ s(p₃, p₁) ∉ F := by
  have hv : (B - C : ℝ × ℝ) ≠ 0 := sub_ne_zero.mpr hBC
  let P₁ : ℝ → ℝ × ℝ := fun α => A - (2*α) • (B - C)
  let P₂ : ℝ → ℝ × ℝ := fun α => A + (2*(1-α)) • (B - C)
  let P₃ : ℝ → ℝ × ℝ := fun α => (2:ℝ) • C - A + (2*α) • (B - C)
  have hP1inj : Function.Injective P₁ := by
    intro a b h
    simp only [P₁] at h
    have hx : (2*a) • (B - C) = (2*b) • (B - C) := sub_right_inj.mp h
    have hzero : (2*a - 2*b) • (B - C) = 0 := by rw [sub_smul, hx, sub_self]
    rcases smul_eq_zero.mp hzero with hc | hv0
    · linarith
    · exact absurd hv0 hv
  have hP2inj : Function.Injective P₂ := by
    intro a b h
    simp only [P₂] at h
    have hx : (2*(1-a)) • (B - C) = (2*(1-b)) • (B - C) := by
      have := congrArg (fun t => t - A) h; simpa using this
    have hzero : (2*(1-a) - 2*(1-b)) • (B - C) = 0 := by rw [sub_smul, hx, sub_self]
    rcases smul_eq_zero.mp hzero with hc | hv0
    · linarith
    · exact absurd hv0 hv
  have hP3inj : Function.Injective P₃ := by
    intro a b h
    simp only [P₃] at h
    have hx : (2*a) • (B - C) = (2*b) • (B - C) := by
      have := congrArg (fun t => t - ((2:ℝ) • C - A)) h; simpa using this
    have hzero : (2*a - 2*b) • (B - C) = 0 := by rw [sub_smul, hx, sub_self]
    rcases smul_eq_zero.mp hzero with hc | hv0
    · linarith
    · exact absurd hv0 hv
  have hP1sub : ∀ a b : ℝ, P₁ a - P₁ b = (2*(b-a)) • (B - C) := by
    intro a b; simp only [P₁]; ext <;> simp <;> ring
  have hP2sub : ∀ a b : ℝ, P₂ a - P₂ b = (2*(b-a)) • (B - C) := by
    intro a b; simp only [P₂]; ext <;> simp <;> ring
  have hP3sub : ∀ a b : ℝ, P₃ a - P₃ b = (2*(a-b)) • (B - C) := by
    intro a b; simp only [P₃]; ext <;> simp <;> ring
  have hA1 : ({α | s(P₁ α, P₂ α) ∈ F} : Set ℝ).Finite :=
    exists_triangle_through_three_points_avoiding_finite_preimage_finset_sym2 P₁ P₂ hP1inj F
  have hA2 : ({α | s(P₂ α, P₃ α) ∈ F} : Set ℝ).Finite :=
    exists_triangle_through_three_points_avoiding_finite_preimage_finset_sym2 P₂ P₃ hP2inj F
  have hA3 : ({α | s(P₃ α, P₁ α) ∈ F} : Set ℝ).Finite :=
    exists_triangle_through_three_points_avoiding_finite_preimage_finset_sym2 P₃ P₁ hP3inj F
  have hA4 : ({α : ℝ | P₂ α = P₃ α}).Finite := by
    have hsub : ({α : ℝ | P₂ α = P₃ α}).Subsingleton := by
      intro a ha b hb
      have heq : P₂ a - P₂ b = P₃ a - P₃ b := by rw [ha, hb]
      rw [hP2sub, hP3sub] at heq
      have hzero : (2*(b-a) - 2*(a-b)) • (B - C) = 0 := by rw [sub_smul, heq, sub_self]
      have h4 : (4*(b-a)) • (B - C) = 0 := by
        rwa [show 2*(b-a) - 2*(a-b) = 4*(b-a) by ring] at hzero
      rcases smul_eq_zero.mp h4 with hs | hv0
      · linarith
      · exact absurd hv0 hv
    exact hsub.finite
  have hA5 : ({α : ℝ | P₃ α = P₁ α}).Finite := by
    have hsub : ({α : ℝ | P₃ α = P₁ α}).Subsingleton := by
      intro a ha b hb
      have heq : P₃ a - P₃ b = P₁ a - P₁ b := by rw [ha, hb]
      rw [hP3sub, hP1sub] at heq
      have hzero : (2*(a-b) - 2*(b-a)) • (B - C) = 0 := by rw [sub_smul, heq, sub_self]
      have h4 : (4*(a-b)) • (B - C) = 0 := by
        rwa [show 2*(a-b) - 2*(b-a) = 4*(a-b) by ring] at hzero
      rcases smul_eq_zero.mp h4 with hs | hv0
      · linarith
      · exact absurd hv0 hv
    exact hsub.finite
  let Bad : Set ℝ :=
    {α | s(P₁ α, P₂ α) ∈ F} ∪ {α | s(P₂ α, P₃ α) ∈ F} ∪ {α | s(P₃ α, P₁ α) ∈ F}
      ∪ {α | P₂ α = P₃ α} ∪ {α | P₃ α = P₁ α}
  have hBad : Bad.Finite := by
    simp only [Bad]
    exact (((hA1.union hA2).union hA3).union hA4).union hA5
  obtain ⟨α, hα1, hα2⟩ :=
    Set.Infinite.exists_notMem_finite (Set.Ioo_infinite (by norm_num : (0:ℝ) < 1)) hBad
  have hP12 : P₁ α ≠ P₂ α := by
    intro h
    have hsub : P₁ α - P₂ α = (-2:ℝ) • (B - C) := by
      simp only [P₁, P₂]; ext <;> simp <;> ring
    rw [h, sub_self] at hsub
    have : (B - C : ℝ × ℝ) = 0 := by
      rcases smul_eq_zero.mp hsub.symm with h1 | h2
      · norm_num at h1
      · exact h2
    exact hv this
  refine ⟨P₁ α, P₂ α, P₃ α, hP12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hα2
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq]; tauto
  · intro h; apply hα2
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq]; tauto
  · rw [openSegment_eq_image]
    refine ⟨α, hα1, ?_⟩
    simp only [P₁, P₂]; ext <;> simp <;> ring
  · rw [openSegment_eq_image]
    refine ⟨1/2, by norm_num, ?_⟩
    simp only [P₂, P₃]; ext <;> simp <;> ring
  · rw [openSegment_eq_image]
    refine ⟨1/2, by norm_num, ?_⟩
    simp only [P₃, P₁]; ext <;> simp <;> ring
  · intro h; apply hα2
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq]; tauto
  · intro h; apply hα2
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq]; tauto
  · intro h; apply hα2
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq]; tauto
