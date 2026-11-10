import AFTD.Prelude
import AFTD.Kb.Tcs.ApnFamilyFa

/-!
# apn_family_fa_component_eq_cubic

Topic: cryptography   Node: bf20f9a95bec

Provenance: helper lemma. arXiv:2611.10269 Sec. 7

Let a and β be elements of a finite field E of characteristic 2 such that the absolute trace of β * a⁻¹ is 0. Then for all x in E, the trace of β * F_a(x) equals the trace of β * x^3.
-/

/-- On the hyperplane of elements orthogonal to a⁻¹, the component of F_a coincides with that of x^3. -/
theorem apn_family_fa_component_eq_cubic {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E] (a β : E) (hH : Algebra.trace (ZMod 2) E (β * a⁻¹) = 0) (x : E) : Algebra.trace (ZMod 2) E (β * apn_family_fa E a x) = Algebra.trace (ZMod 2) E (β * x ^ 3) := by
  unfold apn_family_fa
  have h1 : β * (x ^ 3 + a⁻¹ * algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9)))
      = β * x ^ 3 + algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9)) * (β * a⁻¹) := by
    rw [mul_add]; ring
  rw [h1, map_add]
  have h2 : Algebra.trace (ZMod 2) E (algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9)) * (β * a⁻¹)) = 0 := by
    have hc : Algebra.trace (ZMod 2) E (algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9)) * (β * a⁻¹))
        = Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9) * Algebra.trace (ZMod 2) E (β * a⁻¹) := by
      rw [← Algebra.smul_def, LinearMap.map_smul]; rfl
    rw [hc, hH, mul_zero]
  rw [h2, add_zero]
