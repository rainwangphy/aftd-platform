import AFTD.Prelude

/-!
# three_qubit_weighted_pair_path_zero

Topic: quantum   Node: 8b4467c6f992

Provenance: helper lemma.

The unnormalized weighted exchange path preserves a zero bilinear pair correlation when both directed pairings vanish.
-/

theorem three_qubit_weighted_pair_path_zero
    (A : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (hab : (∑ i, ∑ j, a i * A i j * b j) = 0)
    (hba : (∑ i, ∑ j, b i * A i j * a j) = 0) (t : ℝ) :
    (∑ i, ∑ j, ((1-t)*a i+t*b i) * A i j *
      (-(∑ k, ∑ l, b k * A k l * b l)*t*a j +
        (∑ k, ∑ l, a k * A k l * a l)*(1-t)*b j)) = 0 := by
  let pair := fun (x y : Fin 3 → ℝ) => ∑ i, ∑ j, x i * A i j * y j
  change pair a b = 0 at hab
  change pair b a = 0 at hba
  change pair (fun i => (1-t)*a i+t*b i)
    (fun i => -(pair b b)*t*a i + (pair a a)*(1-t)*b i) = 0
  have hid : pair (fun i => (1-t)*a i+t*b i)
        (fun i => -(pair b b)*t*a i + (pair a a)*(1-t)*b i) =
      (1-t)*(-(pair b b)*t)*(pair a a) +
      (1-t)*(pair a a)*(1-t)*(pair a b) +
      t*(-(pair b b)*t)*(pair b a) +
      t*(pair a a)*(1-t)*(pair b b) := by
    simp [pair, Fin.sum_univ_succ]
    ring
  rw [hid, hab, hba]
  ring
