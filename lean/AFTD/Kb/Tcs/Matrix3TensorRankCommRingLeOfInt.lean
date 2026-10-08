import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankLe
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.Matrix3TensorRankLeOfSurjective
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_tensor_rank_comm_ring_le_of_int

Topic: algebraic_complexity   Node: b05767be7f13

Provenance: formalization of a published result. Source: Bürgisser, Clausen, Shokrollahi, Algebraic Complexity Theory (1997), Proposition 14.1

For any commutative ring R and any natural number r, if 3x3 matrix multiplication has tensor rank at most r over the integers, then 3x3 matrix multiplication has tensor rank at most r over R.
-/

/-- Mapping a triad twice is mapping it by the composite (`matrix3_triad_map` and
`eval_matrix3_decomposition_map` come from the module of `matrix3_tensor_rank_le_of_surjective`). -/
theorem matrix3_triad_map_comp {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] (g : S →+* T) (f : R →+* S) (t : Matrix3Triad R) :
    matrix3_triad_map g (matrix3_triad_map f t) = matrix3_triad_map (g.comp f) t := by
  cases t
  simp [matrix3_triad_map, Matrix.map_map]

theorem matrix3_triad_map_C_comp {σ S : Type*} [CommRing S] (f : MvPolynomial σ ℤ →+* S)
    (L : List (Matrix3Triad ℤ)) :
    (L.map (matrix3_triad_map (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))).map
      (matrix3_triad_map f) = L.map (matrix3_triad_map (Int.castRingHom S)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, matrix3_triad_map_comp]
  congr 1
  exact RingHom.ext_int _ _

/-- Tensor rank upper bounds for 3x3 matrix multiplication transfer from the integers to every commutative ring. -/
theorem matrix3_tensor_rank_comm_ring_le_of_int (R : Type*) [CommRing R]
    (r : ℕ) (h : matrix3_tensor_rank_le ℤ r) :
    matrix3_tensor_rank_le R r := by
  obtain ⟨L, hlen, hL⟩ := h
  -- the identity holds for the generic matrices over `MvPolynomial ℤ`
  set P := MvPolynomial (Bool × Fin 3 × Fin 3) ℤ
  set X : Matrix (Fin 3) (Fin 3) P := fun i j => MvPolynomial.X (false, i, j) with hX
  set Y : Matrix (Fin 3) (Fin 3) P := fun i j => MvPolynomial.X (true, i, j) with hY
  set LP := L.map (matrix3_triad_map (MvPolynomial.C : ℤ →+* P)) with hLP
  have hgen : eval_matrix3_decomposition LP X Y = X * Y := by
    refine Matrix.ext fun i j => ?_
    apply MvPolynomial.funext
    intro x
    have h1 := congrFun (congrFun (eval_matrix3_decomposition_map (MvPolynomial.eval x) LP X Y) i) j
    rw [Matrix.map_apply] at h1
    rw [h1, hLP, matrix3_triad_map_C_comp, ← Matrix.map_apply (f := MvPolynomial.eval x), Matrix.map_mul]
    have hid : Int.castRingHom ℤ = RingHom.id ℤ := RingHom.ext_int _ _
    have hLid : L.map (matrix3_triad_map (Int.castRingHom ℤ)) = L := by
      rw [hid]
      conv_rhs => rw [← List.map_id L]
      apply List.map_congr_left
      intro t _
      cases t
      simp [matrix3_triad_map]
    rw [hLid, hL]
  refine ⟨L.map (matrix3_triad_map (Int.castRingHom R)), by simpa using hlen, ?_⟩
  intro A B
  set f : P →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun x => if x.1 then B x.2.1 x.2.2 else A x.2.1 x.2.2) with hf
  have hXA : X.map f = A := Matrix.ext fun i j => by
    rw [Matrix.map_apply, hf, hX, MvPolynomial.eval₂Hom_X']; rfl
  have hYB : Y.map f = B := Matrix.ext fun i j => by
    rw [Matrix.map_apply, hf, hY, MvPolynomial.eval₂Hom_X']; rfl
  have := eval_matrix3_decomposition_map f LP X Y
  rw [hgen, Matrix.map_mul, hXA, hYB, hLP, matrix3_triad_map_C_comp] at this
  exact this.symm
