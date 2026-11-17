import AFTD.Prelude

/-!
# finite_field_shear_red_difference_obstruction

Topic: combinatorics   Node: 5c95924fff89

Provenance: helper lemma. OP-1482; red-difference condition for the finite-field shear route

For a prime congruent to three modulo four, suppose a coloring pulled back through the scalar function x+y+x squared contains no false unit triple. If r is false and u is a nonzero coordinate of a unit vector, then r+2u squared is true.
-/

theorem finite_field_shear_red_difference_obstruction (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (c : ZMod p → Bool)
    (hred : ∀ x v : Fin 2 → ZMod p, (∑ i : Fin 2, (v i)^2) = 1 →
      ¬ ∀ k : Fin 3, c ((x 0 + (k.val : ZMod p) * v 0) +
        (x 1 + (k.val : ZMod p) * v 1) +
        (x 0 + (k.val : ZMod p) * v 0)^2) = false)
    (u v r : ZMod p) (hu : u ≠ 0) (hv : u^2 + v^2 = 1)
    (hr : c r = false) : c (r + 2 * u^2) = true := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    omega
  let a : ZMod p := (-u^2-u-v) / (2*u)
  have ha : 2*a*u = -u^2-u-v := by
    dsimp [a]
    field_simp
    <;> ring
  let X : Fin 2 → ZMod p := ![a, r-a-a^2]
  let V : Fin 2 → ZMod p := ![u,v]
  have hV : (∑ i : Fin 2, (V i)^2) = 1 := by simpa [V, Fin.sum_univ_two] using hv
  have hpoly (k : ZMod p) :
      (X 0 + k * V 0) + (X 1 + k * V 1) + (X 0 + k * V 0)^2 =
        r + u^2 * (k^2-k) := by
    simp only [X, V, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k * ha
  apply Bool.eq_true_of_not_eq_false
  intro hfalse
  apply hred X V hV
  intro k
  rw [hpoly (k.val : ZMod p)]
  fin_cases k
  · simpa using hr
  · simpa using hr
  · convert hfalse using 1 <;> simp <;> ring
