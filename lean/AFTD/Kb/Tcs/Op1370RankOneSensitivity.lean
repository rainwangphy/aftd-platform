import AFTD.Prelude

/-!
# op1370_rank_one_sensitivity

Topic: combinatorics   Node: 985bfd719379

Provenance: helper lemma.

A nontrivial rank-one perturbation changes a scalar observable when the two associated response factors are nonzero.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_sensitivity
    {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (l r w b x y z : ι → K) (t : K)
    (hinj : Function.Injective (A.mulVec))
    (hx : A.mulVec x = b) (hy : A.mulVec y = l)
    (hz : A.mulVec z + (t * (r ⬝ᵥ z)) • l = b)
    (ht : t ≠ 0) (hwy : w ⬝ᵥ y ≠ 0) (hrx : r ⬝ᵥ x ≠ 0) :
    w ⬝ᵥ z ≠ w ⬝ᵥ x := by
  have hvec : z + (t * (r ⬝ᵥ z)) • y = x := by
    apply hinj
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hy, hx]
    exact hz
  intro hsame
  have hd := congrArg (fun v => w ⬝ᵥ v) hvec
  rw [dotProduct_add, dotProduct_smul] at hd
  simp only [smul_eq_mul, hsame] at hd
  have hp : (t * (r ⬝ᵥ z)) * (w ⬝ᵥ y) = 0 := add_eq_left.mp hd
  have hrz : r ⬝ᵥ z = 0 := by
    have := (mul_eq_zero.mp hp).resolve_right hwy
    exact (mul_eq_zero.mp this).resolve_left ht
  simp [hrz] at hvec
  exact hrx (by rw [← hvec]; exact hrz)
