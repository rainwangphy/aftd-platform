import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.Tensor3Pure
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt

/-!
# linear_flattening_testable_zero_order

Topic: algebraic_complexity   Node: b74529439a0c

Provenance: helper lemma. step towards linear_flattening_testable_even_step

For every n ≥ 1, σ_0((ℂⁿ)⊗³) is testable by the linear flattening method (some linear flattening has potency greater than 0), so the predicate `linear_flattening_testable` is not vacuously false.
-/

/-- Non-vacuity of the testability predicate: for every n ≥ 1 the order-0 case holds. -/
theorem linear_flattening_testable_zero_order (n : ℕ) (hn : 1 ≤ n) :
    linear_flattening_testable n 0 := by
  let L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin 1) (Fin 1) ℂ :=
    { toFun := fun A => fun _ _ => A ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩,
      map_add' := by intro a b; ext i j; rfl,
      map_smul' := by intro c a; ext i j; rfl }
  refine ⟨1, 1, L, (fun _ _ _ => (1 : ℂ)), ?_⟩
  intro x y z
  have hLT : L (fun _ _ _ => (1 : ℂ)) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    simp only [Subsingleton.elim i j, ↓reduceIte]
    rfl
  rw [hLT, Matrix.rank_one]
  simp
