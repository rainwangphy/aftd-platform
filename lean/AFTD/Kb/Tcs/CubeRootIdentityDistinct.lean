import AFTD.Prelude

/-!
# cube_root_identity_distinct

Topic: graphs   Node: 72c39f5e37ef

Provenance: formalization of a published result. Source: arXiv:2610.41820 Lemma 2.4, Eq. (15)

If ω is a primitive cube root of unity in ℂ and x, y ∈ {1, ω, ω^2} are distinct, then (x - y)^2 = -3xy.
-/

/-- On the cube roots of unity, the squared difference of distinct elements is -3 times their product. -/
theorem cube_root_identity_distinct (ω x y : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (hx : x ∈ ({1, ω, ω ^ 2} : Set ℂ)) (hy : y ∈ ({1, ω, ω ^ 2} : Set ℂ)) (hxy : x ≠ y) :
    (x - y) ^ 2 = -3 * x * y := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · rw [hx, hy] at hxy; contradiction
  · rw [hx, hy]; linear_combination hω
  · rw [hx, hy]; linear_combination (ω ^ 2 - ω + 1) * hω
  · rw [hx, hy]; linear_combination hω
  · rw [hx, hy] at hxy; contradiction
  · rw [hx, hy]; linear_combination ω ^ 2 * hω
  · rw [hx, hy]; linear_combination (ω ^ 2 - ω + 1) * hω
  · rw [hx, hy]; linear_combination ω ^ 2 * hω
  · rw [hx, hy] at hxy; contradiction
