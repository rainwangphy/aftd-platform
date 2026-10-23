import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_testable_dim_zero

Topic: algebraic_complexity   Node: a9b6dbf6db77

Provenance: helper lemma. step towards linear_flattening_testable_even_step

At dimension n = 0 the secant variety σ_r((ℂ⁰)⊗³) is never testable by the linear flattening method, for any r: the tensor space is a subsingleton, so every linear flattening has rank 0 on every tensor.
-/

/-- Degenerate small instance: on the zero-dimensional tensor space everything is 0, so no order is testable; this pins down where the definition starts having content. -/
theorem linear_flattening_testable_dim_zero (r : ℕ) : ¬ linear_flattening_testable 0 r := by
  intro ⟨u, v, L, T, hT⟩
  have hT0 : T = 0 := by
    ext i
    exact i.elim0
  have hpure : tensor3_pure (fun (i : Fin 0) => (0 : ℂ)) (fun i => 0) (fun i => 0) = 0 := by
    ext i
    exact i.elim0
  have key := hT (fun i => 0) (fun i => 0) (fun i => 0)
  rw [hT0, hpure, map_zero, Matrix.rank_zero] at key
  omega
