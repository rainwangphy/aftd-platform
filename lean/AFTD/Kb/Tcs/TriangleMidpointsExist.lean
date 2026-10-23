import AFTD.Prelude

/-!
# triangle_midpoints_exist

Topic: combinatorics   Node: 0093125d3ef1

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

For any three pairwise distinct points A, B, C in ℝ², there exist three distinct points p₁, p₂, p₃ forming a triangle whose open sides contain A, B, and C as their midpoints.
-/

/-- For any three pairwise distinct points A, B, C in ℝ², there exist three distinct points p₁, p₂, p₃ forming a triangle whose open sides contain A, B, and C as their midpoints. -/
theorem triangle_midpoints_exist (A B C : ℝ × ℝ) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    ∃ p₁ p₂ p₃ : ℝ × ℝ, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₃ ≠ p₁ ∧
      A ∈ openSegment ℝ p₁ p₂ ∧ B ∈ openSegment ℝ p₂ p₃ ∧ C ∈ openSegment ℝ p₃ p₁ := by
  refine ⟨A + C - B, A + B - C, B + C - A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hBC
    have h1 : (A + C - B).1 = (A + B - C).1 := by rw [h]
    have h2 : (A + C - B).2 = (A + B - C).2 := by rw [h]
    simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] at h1 h2
    ext <;> linarith
  · intro h
    apply hCA
    have h1 : (A + B - C).1 = (B + C - A).1 := by rw [h]
    have h2 : (A + B - C).2 = (B + C - A).2 := by rw [h]
    simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] at h1 h2
    ext <;> linarith
  · intro h
    apply hAB
    have h1 : (B + C - A).1 = (A + C - B).1 := by rw [h]
    have h2 : (B + C - A).2 = (A + C - B).2 := by rw [h]
    simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] at h1 h2
    ext <;> linarith
  · have h1 : A + C - B = A - (B - C) := by abel
    have h2 : A + B - C = A + (B - C) := by abel
    rw [h1, h2]
    exact mem_openSegment_sub_add A (B - C)
  · have h1 : A + B - C = B - (C - A) := by abel
    have h2 : B + C - A = B + (C - A) := by abel
    rw [h1, h2]
    exact mem_openSegment_sub_add B (C - A)
  · have h1 : B + C - A = C - (A - B) := by abel
    have h2 : A + C - B = C + (A - B) := by abel
    rw [h1, h2]
    exact mem_openSegment_sub_add C (A - B)
