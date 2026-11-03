import AFTD.Prelude

/-!
# cube_root_four_cycle_identity

Topic: graphs   Node: d072ff19907b

Provenance: formalization of a published result. Source: arXiv:2610.41820 Lemma 2.4, Eq. (16)

If ω is a primitive cube root of unity in ℂ and a, b, c, d ∈ {1, ω, ω^2} satisfy a ≠ b, b ≠ c, c ≠ d, and d ≠ a, then (a - b)(b - c)(c - d) = 3bc(a - d).
-/

/-- Cyclic difference identity for four elements in the cube roots of unity. -/
theorem cube_root_four_cycle_identity (ω a b c d : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (ha : a ∈ ({1, ω, ω ^ 2} : Set ℂ)) (hb : b ∈ ({1, ω, ω ^ 2} : Set ℂ))
    (hc : c ∈ ({1, ω, ω ^ 2} : Set ℂ)) (hd : d ∈ ({1, ω, ω ^ 2} : Set ℂ))
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    (a - b) * (b - c) * (c - d) = 3 * b * c * (a - d) := by
  have hcube : ∀ x ∈ ({1, ω, ω ^ 2} : Set ℂ), x ^ 3 = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; ring
    · rw [hx]; linear_combination (ω - 1) * hω
    · rw [hx]; linear_combination (ω - 1) * (ω ^ 3 + 1) * hω
  have hpair : ∀ x y : ℂ, x ∈ ({1, ω, ω ^ 2} : Set ℂ) →
      y ∈ ({1, ω, ω ^ 2} : Set ℂ) → x ≠ y → x ^ 2 + x * y + y ^ 2 = 0 := by
    intro x y hx hy hxy
    have hx3 : x ^ 3 = 1 := hcube x hx
    have hy3 : y ^ 3 = 1 := hcube y hy
    have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
      calc
        (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 := by ring
        _ = 0 := by rw [hx3, hy3]; ring
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hxy)
  have h1 : a ^ 2 + a * b + b ^ 2 = 0 := hpair a b ha hb hab
  have h2 : b ^ 2 + b * c + c ^ 2 = 0 := hpair b c hb hc hbc
  have h3 : c ^ 2 + c * d + d ^ 2 = 0 := hpair c d hc hd hcd
  have h4 : d ^ 2 + d * a + a ^ 2 = 0 := hpair d a hd ha hda
  linear_combination (a + b + d) * h1 + (-2 * a - b) * h2 +
    (a + 2 * b) * h3 + (-a - 2 * b) * h4
