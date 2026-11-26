import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2YesInstance
import AFTD.Kb.Tcs.Ks2InstanceVector
import AFTD.Kb.Tcs.Ks2InstanceOuter

/-!
# ks2_yes_instance_single_unit_vector_iff

Topic: np_completeness   Node: 55ad55ca6006

Provenance: helper lemma. Sanity lemma for the definitions ks2_yes_instance, ks2_instance_vector, ks2_instance_outer, serving OP-2182.

Sanity check: for every real c, the one-vector instance in dimension 1 with α = 1 whose only vector is (1), encoded as (1, [(1, 0)]), is a yes-instance ks2_yes_instance c 1 1 [(1, [(1, 0)])] if and only if 1 ≤ c.
-/

theorem ks2_yes_instance_single_unit_vector_iff (c : ℝ) :
    ks2_yes_instance c 1 1 [(1, [(1, 0)])] ↔ 1 ≤ c := by
  have hv : ks2_instance_vector 1 (1, [(1, 0)]) = fun _ => 1 := by
    funext j; fin_cases j; simp [ks2_instance_vector]
  have ho : ks2_instance_outer 1 (1, [(1, 0)]) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [ks2_instance_outer, hv, Matrix.vecMulVec_apply]
  have hn : ∀ b : Bool, ‖Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℂ)
      ((if b then (1 : ℂ) else -1) • (1 : Matrix (Fin 1) (Fin 1) ℂ))‖ = 1 := by
    intro b
    rw [map_smul, map_one, norm_smul, norm_one]
    cases b <;> simp
  constructor
  · rintro ⟨-, -, -, s, hs, h⟩
    match s, hs with
    | [b], _ =>
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        add_zero, ho, hn, Rat.cast_one, Real.sqrt_one, mul_one] at h
      exact h
  · intro h
    refine ⟨by norm_num, by simp [hv], by simp [ho], [true], rfl, ?_⟩
    have h1 := hn true
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
      add_zero, ho, Rat.cast_one, Real.sqrt_one, mul_one, ↓reduceIte] at h1 ⊢
    rw [h1]
    exact h
