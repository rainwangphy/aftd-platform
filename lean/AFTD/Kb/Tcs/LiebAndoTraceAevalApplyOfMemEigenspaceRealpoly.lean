import AFTD.Prelude

/-!
# LiebAndoTrace.aeval_apply_of_mem_eigenspace_realpoly

Topic: quantum   Node: a94ad8f8905e

Provenance: formalization of a published result. Source: QuantumInfo, `LiebAndoTrace.aeval_apply_of_mem_eigenspace_realpoly`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LiebAndoTrace.aeval_apply_of_mem_eigenspace_realpoly
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open Module.End Polynomial in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ] in
lemma LiebAndoTrace.aeval_apply_of_mem_eigenspace_realpoly
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) (p : ℝ[X]) :
    Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
      ((p.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
        Polynomial.aeval T.toLinearMap (p.map (algebraMap ℝ ℂ)) x := by
    simpa using
      congrArg (fun F : 𝓚 →ₗ[ℂ] 𝓚 => F x)
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℂ) (S := 𝓚 →L[ℂ] 𝓚) (T := ℂ) (U := 𝓚 →ₗ[ℂ] 𝓚)
          (φ := RingHom.id ℂ) (ψ := ContinuousLinearMap.toLinearMapRingHom)
          (h := by ext z; rfl) (p := p.map (algebraMap ℝ ℂ)) (a := T))
  rw [hmap]
  simpa using
    (Module.End.aeval_apply_of_hasEigenvector
      (f := T.toLinearMap) (p := p.map (algebraMap ℝ ℂ)) (μ := (r : ℂ)) (x := x) ⟨hx, hx0⟩)

-- The interpolation-based `cfcR`-on-eigenspace lemma is elaboration-heavy.
