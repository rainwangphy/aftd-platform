import AFTD.Prelude
import AFTD.Kb.Tcs.LowMul3Target2
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.G

/-!
# low_mul3_target2_not_mem_degree_two

Topic: circuits   Node: 7403bb2fcf74

Provenance: helper lemma. arXiv:2611.15992 Section 5 (Proof of Theorem 8)

The target function z_2 of the three-bit low-half multiplier does not lie in the space of functions of degree at most 2 over ZMod 2.
-/

open BigOperators

/-- The index set of the quartic monomial in `lowMul3Target2`. -/
def low_mul3_target2_S4 : Finset (Fin 6) := {0, 1, 3, 4}

/-- The indicator assignment of a subset `T ⊆ Fin 6`. -/
def low_mul3_target2_indicator (T : Finset (Fin 6)) : Fin 6 → Bool :=
  fun i => i ∈ T

/-- A multilinear monomial function corresponding to subset `U ⊆ Fin 6`. -/
def low_mul3_target2_monomialFn (U : Finset (Fin 6)) : (Fin 6 → Bool) → ZMod 2 :=
  fun x => ∏ i ∈ U, if x i = true then 1 else 0

/-- The linear functional evaluating a Boolean function on the subcube spanned by `low_mul3_target2_S4`. -/
def low_mul3_target2_L_lin : ((Fin 6 → Bool) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ T ∈ low_mul3_target2_S4.powerset, LinearMap.proj (low_mul3_target2_indicator T)

theorem low_mul3_target2_L_lin_apply (f : (Fin 6 → Bool) → ZMod 2) :
    low_mul3_target2_L_lin f = ∑ T ∈ low_mul3_target2_S4.powerset, f (low_mul3_target2_indicator T) := by
  simp [low_mul3_target2_L_lin]

theorem low_mul3_target2_L_monomial_eq_zero :
    ∀ U : Finset (Fin 6), U.card ≤ 2 →
      (∑ T ∈ low_mul3_target2_S4.powerset, low_mul3_target2_monomialFn U (low_mul3_target2_indicator T)) = 0 := by
  decide

theorem low_mul3_target2_L_lin_zero_of_mem_degreeSpace {f : (Fin 6 → Bool) → ZMod 2}
    (hf : f ∈ degreeSpace (ZMod 2) (Fin 6) 2) : low_mul3_target2_L_lin f = 0 := by
  refine Submodule.span_induction (p := fun g _ => low_mul3_target2_L_lin g = 0) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨U, hU, rfl⟩
    rw [low_mul3_target2_L_lin_apply]
    exact low_mul3_target2_L_monomial_eq_zero U hU
  · exact low_mul3_target2_L_lin.map_zero
  · intro x y hx hy hx0 hy0
    rw [low_mul3_target2_L_lin.map_add, hx0, hy0, add_zero]
  · intro a x hx hx0
    rw [low_mul3_target2_L_lin.map_smul, hx0, smul_zero]

theorem low_mul3_target2_L_lin_target2 : low_mul3_target2_L_lin lowMul3Target2 = 1 := by
  rw [low_mul3_target2_L_lin_apply]
  decide

/-- The target output z_2 does not belong to degreeSpace 2 because its algebraic normal form has degree 4. -/
theorem low_mul3_target2_not_mem_degree_two :
    lowMul3Target2 ∉ degreeSpace (ZMod 2) (Fin 6) 2 := by
  intro h
  have h0 := low_mul3_target2_L_lin_zero_of_mem_degreeSpace h
  have h1 := low_mul3_target2_L_lin_target2
  rw [h0] at h1
  revert h1
  decide
