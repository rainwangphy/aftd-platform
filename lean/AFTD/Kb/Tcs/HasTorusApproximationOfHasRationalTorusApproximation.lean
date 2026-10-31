import AFTD.Prelude
import AFTD.Kb.Tcs.HasRationalTorusApproximation
import AFTD.Kb.Tcs.HasTorusApproximation
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.Bit

/-!
# hasTorusApproximation_of_hasRationalTorusApproximation

Topic: circuits   Node: 06cc47bfe499

Provenance: helper lemma. step towards op_729_torus_degree_n_sub_two_exact_anf_spectrum

For any Boolean function f on n variables, natural degree d, and error ε, if f has a rational torus approximation of degree d with error ε, then f has a real torus approximation of degree d with error ε.
-/

/-- A rational torus approximation of degree d and error ε induces a real torus approximation with the same parameters. -/
theorem hasTorusApproximation_of_hasRationalTorusApproximation {n : ℕ}
    (f : (Fin n → Bool) → Bool) (d : ℕ) (ε : ℝ)
    (h : HasRationalTorusApproximation f d ε) :
    HasTorusApproximation f d ε := by
  obtain ⟨P, hP, Z, hZ⟩ := h
  let F : ((Fin n → Bool) → ℚ) →ₗ[ℚ] ((Fin n → Bool) → ℝ) :=
    { toFun := fun p x => (p x : ℝ)
      map_add' := by intro p q; funext x; simp
      map_smul' := by intro a p; funext x; simp [Algebra.smul_def, Rat.cast_mul] }
  have hmem : (fun x => (P x : ℝ)) ∈ degreeSpace ℝ (Fin n) d := by
    let p : ((Fin n → Bool) → ℚ) → Prop := fun x => F x ∈ degreeSpace ℝ (Fin n) d
    have hgen : ∀ x ∈ ({f : (Fin n → Bool) → ℚ | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = fun x => ∏ i ∈ S, if x i = true then 1 else 0} : Set _), p x := by
      rintro g ⟨S, hS, rfl⟩
      have hcast : F (fun x => ∏ i ∈ S, if x i = true then (1:ℚ) else 0)
          = fun x => ∏ i ∈ S, if x i = true then (1:ℝ) else 0 := by
        funext x
        simp only [F, LinearMap.coe_mk, AddHom.coe_mk]
        push_cast
        apply Finset.prod_congr rfl
        intro i hi
        split <;> simp
      show F _ ∈ degreeSpace ℝ (Fin n) d
      rw [hcast]
      exact Submodule.subset_span ⟨S, hS, rfl⟩
    have h := Submodule.span_induction (R := ℚ) (s := ({f : (Fin n → Bool) → ℚ | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = fun x => ∏ i ∈ S, if x i = true then 1 else 0} : Set _)) (p := fun x _ => p x) hgen ?_ ?_ ?_ hP
    · simpa [p, F] using h
    · show p 0
      change F 0 ∈ degreeSpace ℝ (Fin n) d
      have h0 : F 0 = 0 := by funext y; simp [F]
      rw [h0]
      exact Submodule.zero_mem _
    · intro x y hx hy hpx hpy
      change F (x + y) ∈ degreeSpace ℝ (Fin n) d
      rw [map_add]
      exact Submodule.add_mem _ hpx hpy
    · intro a x hx hpx
      change F (a • x) ∈ degreeSpace ℝ (Fin n) d
      have : F (a • x) = (a : ℝ) • F x := by
        funext y
        simp [F, Algebra.smul_def, Rat.cast_mul]
      rw [this]
      exact Submodule.smul_mem _ (a : ℝ) hpx
  exact ⟨fun x => (P x : ℝ), hmem, Z, fun x => by simpa using hZ x⟩
