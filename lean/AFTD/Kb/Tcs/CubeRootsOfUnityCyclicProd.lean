import AFTD.Prelude

/-!
# cube_roots_of_unity_cyclic_prod

Topic: graphs   Node: 6c0fccf576bf

Provenance: helper lemma. arXiv:2610.41820 Lemma 2.4(b)

For any complex cube roots of unity a, b, c, d such that adjacent elements are distinct and either a = c or b = d, (a - b) * (b - c) * (c - d) = 3 * b * c * (a - d).
-/

private theorem cube_roots_of_unity_cyclic_prod_adjacent (x y : ℂ)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x ≠ y) :
    (x - y) * (y - x) = 3 * x * y := by
  have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
    have h : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
    rw [← h]
    rw [hx, hy]
    ring
  have hsum : x ^ 2 + x * y + y ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact False.elim (hxy (sub_eq_zero.mp h))
    · exact h
  have h2 : (x - y) * (y - x) - 3 * x * y = 0 := by
    calc
      (x - y) * (y - x) - 3 * x * y = -(x ^ 2 + x * y + y ^ 2) := by ring
      _ = 0 := by rw [hsum]; ring
  exact sub_eq_zero.mp h2

/-- Cyclic product of differences of four cube roots of unity with matching opposite elements. -/
theorem cube_roots_of_unity_cyclic_prod (a b c d : ℂ)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (hd : d ^ 3 = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (h_cases : a = c ∨ b = d) :
    (a - b) * (b - c) * (c - d) = 3 * b * c * (a - d) := by
  rcases h_cases with hac | hbd
  · subst c
    have h : (a - b) * (b - a) = 3 * a * b :=
      cube_roots_of_unity_cyclic_prod_adjacent a b ha hb hab
    calc
      (a - b) * (b - a) * (a - d) = ((a - b) * (b - a)) * (a - d) := by ring
      _ = (3 * a * b) * (a - d) := by rw [h]
      _ = 3 * b * a * (a - d) := by ring
  · subst d
    have h : (b - c) * (c - b) = 3 * b * c :=
      cube_roots_of_unity_cyclic_prod_adjacent b c hb hc hbc
    calc
      (a - b) * (b - c) * (c - b) = (a - b) * ((b - c) * (c - b)) := by ring
      _ = (a - b) * (3 * b * c) := by rw [h]
      _ = 3 * b * c * (a - b) := by ring
