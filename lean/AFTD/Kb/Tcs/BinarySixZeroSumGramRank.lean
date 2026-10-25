import AFTD.Prelude
import AFTD.Kb.Tcs.BinarySixZeroSumDifferencesIndependent

/-!
# binary_six_zero_sum_gram_rank

Topic: quantum   Node: 2213edba13ba

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

The sum of the outer squares of six distinct binary vectors with zero sum has matrix rank exactly four.
-/

theorem binary_six_zero_sum_gram_rank {n : ℕ}
    (v : Fin 6 → (Fin n → ZMod 2))
    (hinj : Function.Injective v) (hsum : ∑ j, v j = 0) :
    (Matrix.of (fun i j => ∑ k : Fin 6, v k i * v k j)).rank = 4 := by
  classical
  let V : Matrix (Fin n) (Fin 4) (ZMod 2) :=
    fun i j => v ⟨j.val + 1, by omega⟩ i + v 0 i
  let J : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    fun i j => if i = j then 0 else 1
  have hLI := binary_six_zero_sum_differences_independent v hinj hsum
  have hV : Function.Injective V.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    change V.mulVec a = 0 at ha
    have hrel : ∑ j : Fin 4, a j • (v ⟨j.val + 1, by omega⟩ + v 0) = 0 := by
      funext i
      have h := congrFun ha i
      simpa [V, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_add] using h
    have hc := Fintype.linearIndependent_iff.mp hLI a hrel
    funext j
    exact hc j
  have hfactor : Matrix.of (fun i j => ∑ k : Fin 6, v k i * v k j) = V * J * V.transpose := by
    ext i j
    have hi := congrFun hsum i
    have hj := congrFun hsum j
    simp [Fin.sum_univ_succ] at hi hj
    have hi5 : v 5 i = v 0 i + v 1 i + v 2 i + v 3 i + v 4 i := by
      linear_combination (norm := ring_nf) hi <;> reduce_mod_char
    have hj5 : v 5 j = v 0 j + v 1 j + v 2 j + v 3 j + v 4 j := by
      linear_combination (norm := ring_nf) hj <;> reduce_mod_char
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
    simp [Fin.sum_univ_succ, V, J, hi5, hj5]
    ring_nf <;> reduce_mod_char
  have hr {k : ℕ} (B : Matrix (Fin 4) (Fin k) (ZMod 2)) :
      (V * B).rank = B.rank := by
    rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective V.mulVecLin hV _).finrank_eq.symm
  have hJ : J.rank = 4 := by
    simpa using Matrix.rank_of_det_ne_zero (show J.det ≠ 0 by decide)
  rw [hfactor, Matrix.mul_assoc, hr, ← Matrix.rank_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, hr, Matrix.rank_transpose, hJ]
