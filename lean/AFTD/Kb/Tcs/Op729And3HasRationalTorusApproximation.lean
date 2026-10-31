import AFTD.Prelude
import AFTD.Kb.Tcs.HasRationalTorusApproximation
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.Bit

/-!
# op_729_and3_has_rational_torus_approximation

Topic: circuits   Node: 9e6066012234

Provenance: helper lemma. arXiv:2610.19174

The 3-variable conjunction function on Fin 3 → Bool has a degree 1 rational torus approximation with error 1/6: HasRationalTorusApproximation (fun x : Fin 3 → Bool => x 0 && x 1 && x 2) 1 (1 / 6).
-/

/-- The 3-variable AND function has a degree 1 rational torus approximation with error 1/6. -/
theorem op_729_and3_has_rational_torus_approximation :
    HasRationalTorusApproximation (fun x : Fin 3 → Bool => x 0 && x 1 && x 2) 1 (1 / 6) := by
  classical
  refine ⟨fun x : Fin 3 → Bool =>
      13/6 - 7/6 * ((if x 0 = true then (1:ℚ) else 0) + (if x 1 = true then (1:ℚ) else 0) + (if x 2 = true then (1:ℚ) else 0)),
    ?_, fun x : Fin 3 → Bool =>
      if x 0 then (if x 1 then (if x 2 then (-2:ℤ) else 0) else (if x 2 then 0 else 1))
        else (if x 1 then (if x 2 then 0 else 1) else (if x 2 then 1 else 2)), ?_⟩
  · have hm0 : (fun _ : Fin 3 → Bool => (1:ℚ)) ∈ degreeSpace ℚ (Fin 3) 1 := by
      refine Submodule.subset_span ⟨∅, by simp, ?_⟩
      funext x; simp
    have hm : ∀ i : Fin 3, (fun x : Fin 3 → Bool => (if x i = true then (1:ℚ) else 0)) ∈
        degreeSpace ℚ (Fin 3) 1 := by
      intro i
      refine Submodule.subset_span ⟨{i}, by simp, ?_⟩
      funext x; simp
    have key : (fun x : Fin 3 → Bool =>
      13/6 - 7/6 * ((if x 0 = true then (1:ℚ) else 0) + (if x 1 = true then (1:ℚ) else 0)
        + (if x 2 = true then (1:ℚ) else 0)))
      = (13/6 : ℚ) • (fun _ : Fin 3 → Bool => (1:ℚ))
        + ((-7/6 : ℚ) • (fun x : Fin 3 → Bool => (if x 0 = true then (1:ℚ) else 0))
        + ((-7/6 : ℚ) • (fun x : Fin 3 → Bool => (if x 1 = true then (1:ℚ) else 0))
        + (-7/6 : ℚ) • (fun x : Fin 3 → Bool => (if x 2 = true then (1:ℚ) else 0)))) := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [key]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hm0)
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (hm 0))
        (Submodule.add_mem _ (Submodule.smul_mem _ _ (hm 1)) (Submodule.smul_mem _ _ (hm 2))))
  · intro x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [h0, h1, h2, bit] <;> norm_num
