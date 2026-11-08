import AFTD.Prelude
import AFTD.Kb.NumberTheory.ViewObstructionRayDist
import AFTD.Kb.NumberTheory.IntToEuclidean
import AFTD.Kb.NumberTheory.ViewObstructionCenter

/-!
# view_obstruction_ray_dist_abs

Topic: elementary_number_theory   Node: e36bdd243b0b

Provenance: formalization of a published result. Source: arXiv:2610.37711 Lemma 2.3(a)

For every integer vector v in ℤ^n with no zero coordinate, the view-obstruction distance d_n(|v|) equals d_n(v).
-/

def view_obstruction_ray_dist_abs_flip_coord (neg : Bool) (z : ℤ) : ℤ :=
  if neg then -z - 1 else z

lemma view_obstruction_ray_dist_abs_flip_coord_involutive (neg : Bool) (z : ℤ) :
    view_obstruction_ray_dist_abs_flip_coord neg (view_obstruction_ray_dist_abs_flip_coord neg z) = z := by
  cases neg <;> simp [view_obstruction_ray_dist_abs_flip_coord]

def view_obstruction_ray_dist_abs_flip_equiv {n : ℕ} (neg : Fin n → Bool) : (Fin n → ℤ) ≃ (Fin n → ℤ) where
  toFun z i := view_obstruction_ray_dist_abs_flip_coord (neg i) (z i)
  invFun z i := view_obstruction_ray_dist_abs_flip_coord (neg i) (z i)
  left_inv z := by ext i; apply view_obstruction_ray_dist_abs_flip_coord_involutive
  right_inv z := by ext i; apply view_obstruction_ray_dist_abs_flip_coord_involutive

lemma view_obstruction_ray_dist_abs_coord_sq_eq (t : ℝ) (v z : ℤ) :
    (t * (v : ℝ) - (1/2 + (view_obstruction_ray_dist_abs_flip_coord (decide (v < 0)) z : ℝ)))^2 =
    (t * ((|v| : ℤ) : ℝ) - (1/2 + (z : ℝ)))^2 := by
  dsimp [view_obstruction_ray_dist_abs_flip_coord]
  split_ifs with h
  · rw [decide_eq_true_iff] at h
    have hv : ((|v| : ℤ) : ℝ) = - (v : ℝ) := by
      push_cast
      exact_mod_cast abs_of_neg h
    rw [hv]
    have : t * (v : ℝ) - (1/2 + ((-z - 1 : ℤ) : ℝ)) = - (t * - (v : ℝ) - (1/2 + (z : ℝ))) := by
      push_cast; ring
    rw [this]
    ring
  · rw [decide_eq_true_iff] at h
    have hv : ((|v| : ℤ) : ℝ) = (v : ℝ) := by
      have : 0 ≤ v := not_lt.mp h
      push_cast
      exact_mod_cast abs_of_nonneg this
    rw [hv]

lemma view_obstruction_ray_dist_abs_norm_sq_eq_sum (n : ℕ) (t : ℝ) (v z : Fin n → ℤ) :
    ‖t • int_to_euclidean n v - (view_obstruction_center n + int_to_euclidean n z)‖ ^ 2 =
    ∑ i, (t * (v i : ℝ) - (1/2 + (z i : ℝ))) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Lemma 2.3(a): View-obstruction distance is invariant under coordinatewise absolute values. -/
theorem view_obstruction_ray_dist_abs
    (n : ℕ) (v : Fin n → ℤ) (hnz : ∀ i, v i ≠ 0) :
    view_obstruction_ray_dist n (fun i => |v i|) = view_obstruction_ray_dist n v := by
  have _ := hnz
  dsimp [view_obstruction_ray_dist]
  congr 1
  ext t
  let e := view_obstruction_ray_dist_abs_flip_equiv (n := n) (fun i => decide (v i < 0))
  conv_rhs => rw [← Equiv.iInf_comp e]
  congr 1
  ext z
  rw [view_obstruction_ray_dist_abs_norm_sq_eq_sum, view_obstruction_ray_dist_abs_norm_sq_eq_sum]
  congr 1
  ext i
  dsimp [e, view_obstruction_ray_dist_abs_flip_equiv]
  exact (view_obstruction_ray_dist_abs_coord_sq_eq t (v i) (z i)).symm
