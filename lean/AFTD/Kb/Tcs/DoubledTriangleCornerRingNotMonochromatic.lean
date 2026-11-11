import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleIsGoodColoring
import AFTD.Kb.Tcs.DoubledTriangleRingIsMonochromatic
import AFTD.Kb.Tcs.DoubledTriangleRing
import AFTD.Kb.Tcs.DoubledTrianglePointToVertex
import AFTD.Kb.Tcs.DoubledTriangleVertex
import AFTD.Kb.Tcs.DoubledTriangleRingFaces
import AFTD.Kb.Tcs.DoubledTriangleFace
import AFTD.Kb.Tcs.DoubledTriangleFaceVertices
import AFTD.Kb.Tcs.DoubledTriangleVertexFaces

/-!
# doubled_triangle_corner_ring_not_monochromatic

Topic: combinatorics   Node: 60c79c86d73e

Provenance: helper lemma. arXiv:2611.12065, Lemma 4.3 proof step 2

For any integer n > 0 and any good coloring C of T(n), the corner ring DoubledTriangleRing.x ⟨n - 1, by omega⟩ is not monochromatic under C.
-/

def doubled_triangle_corner_ring_not_monochromatic_corner_v {n : ℕ} (hn : 0 < n) : DoubledTriangleVertex n :=
  DoubledTriangleVertex.boundary ⟨n, by omega⟩ ⟨0, by omega⟩
    (by show (n : ℕ) + 0 ≤ n; omega)
    (by show (n : ℕ) = 0 ∨ (0 : ℕ) = 0 ∨ (n : ℕ) + 0 = n; omega)

theorem doubled_triangle_corner_ring_not_monochromatic_corner_eq_point_to_vertex_iff
    {n : ℕ} (hn : 0 < n) (front : Bool)
    (a b : Fin (n + 1)) (hab : (a : ℕ) + b ≤ n) :
    doubled_triangle_corner_ring_not_monochromatic_corner_v hn = doubled_triangle_point_to_vertex front a b hab ↔
    (a : ℕ) = n ∧ (b : ℕ) = 0 := by
  unfold doubled_triangle_point_to_vertex doubled_triangle_corner_ring_not_monochromatic_corner_v
  split_ifs with h_bd
  · constructor
    · intro h
      injection h with ha hb
      exact ⟨congr_arg Fin.val ha.symm, congr_arg Fin.val hb.symm⟩
    · rintro ⟨ha, hb⟩
      congr 1
      · ext; exact ha.symm
      · ext; exact hb.symm
  · constructor
    · intro h; contradiction
    · rintro ⟨ha, hb⟩
      exfalso
      apply h_bd
      right; left; exact hb

theorem doubled_triangle_corner_ring_not_monochromatic_up_eq_helper
    {n : ℕ} (hn : 0 < n) (front : Bool) (i j : Fin n) (h : (i : ℕ) + j < n)
    (hi : i = ⟨n - 1, by omega⟩) :
    DoubledTriangleFace.up front i j h =
    DoubledTriangleFace.up front ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega) := by
  have hi_val : (i : ℕ) = n - 1 := congr_arg Fin.val hi
  have hj_val : (j : ℕ) = 0 := by
    have : (i : ℕ) + j < n := h
    omega
  cases i; cases j
  dsimp at hi_val hj_val
  subst hi_val hj_val
  rfl

theorem doubled_triangle_corner_ring_not_monochromatic_mem_ring_faces
    {n : ℕ} (hn : 0 < n) (f : DoubledTriangleFace n) :
    f ∈ doubled_triangle_ring_faces (DoubledTriangleRing.x ⟨n - 1, by omega⟩) ↔
    (f = DoubledTriangleFace.up true ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega) ∨
     f = DoubledTriangleFace.up false ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega)) := by
  dsimp [doubled_triangle_ring_faces]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases f with
  | up front i j h =>
    simp only [beq_iff_eq]
    constructor
    · intro hi
      cases front
      · right; exact doubled_triangle_corner_ring_not_monochromatic_up_eq_helper hn false i j h hi
      · left; exact doubled_triangle_corner_ring_not_monochromatic_up_eq_helper hn true i j h hi
    · rintro (h1 | h2)
      · injection h1
      · injection h2
  | down front i j h =>
    simp only [beq_iff_eq]
    constructor
    · intro hi
      have : (i : ℕ) = n - 1 := congr_arg Fin.val hi
      omega
    · rintro (h1 | h2) <;> contradiction

theorem doubled_triangle_corner_ring_not_monochromatic_mem_vertex_faces
    {n : ℕ} (hn : 0 < n) (f : DoubledTriangleFace n) :
    f ∈ doubled_triangle_vertex_faces (doubled_triangle_corner_ring_not_monochromatic_corner_v hn) ↔
    (f = DoubledTriangleFace.up true ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega) ∨
     f = DoubledTriangleFace.up false ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega)) := by
  dsimp [doubled_triangle_vertex_faces]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases f with
  | up front i j h =>
    dsimp [doubled_triangle_face_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton, doubled_triangle_corner_ring_not_monochromatic_corner_eq_point_to_vertex_iff hn]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have : (i : ℕ) + j < n := h; omega
      · have hi : i = ⟨n - 1, by omega⟩ := by ext; change (i : ℕ) = n - 1; omega
        cases front
        · right; exact doubled_triangle_corner_ring_not_monochromatic_up_eq_helper hn false i j h hi
        · left; exact doubled_triangle_corner_ring_not_monochromatic_up_eq_helper hn true i j h hi
      · have : (i : ℕ) + j < n := h; omega
    · rintro (h1 | h2)
      · right; left
        injection h1 with _ hi hj
        have hi_val : (i : ℕ) = n - 1 := by rw [hi]
        have hj_val : (j : ℕ) = 0 := by rw [hj]
        exact ⟨by omega, by omega⟩
      · right; left
        injection h2 with _ hi hj
        have hi_val : (i : ℕ) = n - 1 := by rw [hi]
        have hj_val : (j : ℕ) = 0 := by rw [hj]
        exact ⟨by omega, by omega⟩
  | down front i j h =>
    dsimp [doubled_triangle_face_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton, doubled_triangle_corner_ring_not_monochromatic_corner_eq_point_to_vertex_iff hn]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have : (i : ℕ) + j + 1 < n := h; omega
      · have : (i : ℕ) + j + 1 < n := h; omega
      · have : (i : ℕ) + j + 1 < n := h; omega
    · rintro (h1 | h2) <;> contradiction

/-- The corner ring X_{n-1} consists of two faces at a degree-2 vertex and is therefore not monochromatic in any good coloring. -/
theorem doubled_triangle_corner_ring_not_monochromatic
    {n : ℕ} (hn : 0 < n) (C : DoubledTriangleFace n → Bool)
    (hC : doubled_triangle_is_good_coloring C) :
    ¬ doubled_triangle_ring_is_monochromatic C (DoubledTriangleRing.x ⟨n - 1, by omega⟩) := by
  let f_front : DoubledTriangleFace n :=
    DoubledTriangleFace.up true ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega)
  let f_back : DoubledTriangleFace n :=
    DoubledTriangleFace.up false ⟨n - 1, by omega⟩ ⟨0, hn⟩ (by show (n - 1) + 0 < n; omega)
  have h_ne : f_front ≠ f_back := by
    intro h; injection h with h; contradiction
  let v := doubled_triangle_corner_ring_not_monochromatic_corner_v hn
  have hv := hC v
  dsimp at hv
  set faces := doubled_triangle_vertex_faces v
  have h_faces : ∀ f, f ∈ faces ↔ f = f_front ∨ f = f_back :=
    doubled_triangle_corner_ring_not_monochromatic_mem_vertex_faces hn
  have h_faces_eq : faces = {f_front, f_back} := by
    ext f; rw [h_faces, Finset.mem_insert, Finset.mem_singleton]
  have h_ring_front : f_front ∈ doubled_triangle_ring_faces (DoubledTriangleRing.x ⟨n - 1, by omega⟩) := by
    rw [doubled_triangle_corner_ring_not_monochromatic_mem_ring_faces hn]
    left; rfl
  have h_ring_back : f_back ∈ doubled_triangle_ring_faces (DoubledTriangleRing.x ⟨n - 1, by omega⟩) := by
    rw [doubled_triangle_corner_ring_not_monochromatic_mem_ring_faces hn]
    right; rfl
  intro h_mono
  dsimp [doubled_triangle_ring_is_monochromatic] at h_mono
  rcases h_mono with h_all_true | h_all_false
  · have hC_front : C f_front = true := h_all_true f_front h_ring_front
    have hC_back : C f_back = true := h_all_true f_back h_ring_back
    have hb_card : (faces.filter (fun f => C f = true)).card = 2 := by
      rw [h_faces_eq]
      have : {f ∈ ({f_front, f_back} : Finset (DoubledTriangleFace n)) | C f = true} = {f_front, f_back} := by
        ext f; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact h.1
        · rintro (rfl | rfl) <;> exact ⟨by simp, by simp [hC_front, hC_back]⟩
      rw [this, Finset.card_pair h_ne]
    have hw_card : (faces.filter (fun f => C f = false)).card = 0 := by
      rw [h_faces_eq]
      have : {f ∈ ({f_front, f_back} : Finset (DoubledTriangleFace n)) | C f = false} = ∅ := by
        ext f; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl), hx⟩
          · simp [hC_front] at hx
          · simp [hC_back] at hx
        · intro h; simp at h
      rw [this, Finset.card_empty]
    rw [hb_card, hw_card] at hv
    have hd := hv.dvd
    rcases hd with ⟨k, hk⟩
    omega
  · have hC_front : C f_front = false := h_all_false f_front h_ring_front
    have hC_back : C f_back = false := h_all_false f_back h_ring_back
    have hb_card : (faces.filter (fun f => C f = true)).card = 0 := by
      rw [h_faces_eq]
      have : {f ∈ ({f_front, f_back} : Finset (DoubledTriangleFace n)) | C f = true} = ∅ := by
        ext f; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl), hx⟩
          · simp [hC_front] at hx
          · simp [hC_back] at hx
        · intro h; simp at h
      rw [this, Finset.card_empty]
    have hw_card : (faces.filter (fun f => C f = false)).card = 2 := by
      rw [h_faces_eq]
      have : {f ∈ ({f_front, f_back} : Finset (DoubledTriangleFace n)) | C f = false} = {f_front, f_back} := by
        ext f; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact h.1
        · rintro (rfl | rfl) <;> exact ⟨by simp, by simp [hC_front, hC_back]⟩
      rw [this, Finset.card_pair h_ne]
    rw [hb_card, hw_card] at hv
    have hd := hv.dvd
    rcases hd with ⟨k, hk⟩
    omega
