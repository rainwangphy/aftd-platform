import AFTD.Prelude
import AFTD.Kb.Tcs.Ndeg
import AFTD.Kb.Tcs.HasNondetPoly
import AFTD.Kb.Tcs.IsNondetPolynomial
import AFTD.Kb.Tcs.FullMonomial
import AFTD.Kb.Tcs.ExplicitApproximantMemDegreeSpace
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.TopCoefficient
import AFTD.Kb.Tcs.G

/-!
# ndeg_le_n

Topic: circuits   Node: b75c2781dcda

Provenance: formalization of a published result. Source: arXiv:2611.11966 Prop 22

For any natural number n and any Boolean function f : (Fin n → Bool) → Bool, the non-deterministic degree of f is at most n.
-/

lemma ndeg_le_n_hasNondetPoly (n : ℕ) (f : (Fin n → Bool) → Bool) : HasNondetPoly f n := by
  use fun x => if f x = true then (1 : ℝ) else 0
  constructor
  · by_cases hn : 0 < n
    · have h1 : (fun x => (if f x = true then 1 else 0) - (topCoefficient f : ℝ) * fullMonomial x) ∈
          degreeSpace ℝ (Fin n) (n - 1) := explicitApproximant_function_sub_top_mem hn f
      have hmono : degreeSpace ℝ (Fin n) (n - 1) ≤ degreeSpace ℝ (Fin n) n := by
        apply Submodule.span_mono
        rintro g ⟨S, hS, rfl⟩
        exact ⟨S, hS.trans (Nat.sub_le n 1), rfl⟩
      have h1' := hmono h1
      have h2 : (fullMonomial : (Fin n → Bool) → ℝ) ∈ degreeSpace ℝ (Fin n) n := by
        apply Submodule.subset_span
        exact ⟨Finset.univ, by simp, rfl⟩
      have h3 : ((topCoefficient f : ℝ) • (fullMonomial : (Fin n → Bool) → ℝ)) ∈ degreeSpace ℝ (Fin n) n :=
        Submodule.smul_mem _ _ h2
      have hsum := Submodule.add_mem _ h1' h3
      have heq : (fun x => if f x = true then (1 : ℝ) else 0) =
          (fun x => (if f x = true then 1 else 0) - (topCoefficient f : ℝ) * fullMonomial x) +
          ((topCoefficient f : ℝ) • (fullMonomial : (Fin n → Bool) → ℝ)) := by
        ext x
        dsimp
        ring
      rw [heq]
      exact hsum
    · have hn0 : n = 0 := by omega
      subst hn0
      have hone : (fun (_ : Fin 0 → Bool) => (1 : ℝ)) ∈ degreeSpace ℝ (Fin 0) 0 := by
        apply Submodule.subset_span
        refine ⟨∅, by simp, ?_⟩
        ext x
        simp
      by_cases h : f (fun _ => false) = true
      · have heq : (fun x => if f x = true then (1 : ℝ) else 0) = (fun _ => 1) := by
          ext x
          have hx : x = (fun _ => false) := by
            ext i
            exact Fin.elim0 i
          rw [hx, h]
          simp
        rw [heq]
        exact hone
      · have heq : (fun x => if f x = true then (1 : ℝ) else 0) = 0 := by
          ext x
          have hx : x = (fun _ => false) := by
            ext i
            exact Fin.elim0 i
          rw [hx]
          have : f (fun _ => false) = false := by
            revert h
            cases f (fun _ => false) <;> simp
          rw [this]
          simp
        rw [heq]
        exact Submodule.zero_mem _
  · intro x
    by_cases hx : f x = true <;> simp [hx]

/-- Every Boolean function on n variables has non-deterministic degree at most n. -/
theorem ndeg_le_n (n : ℕ) (f : (Fin n → Bool) → Bool) : ndeg f ≤ n := by
  have h : HasNondetPoly f n := ndeg_le_n_hasNondetPoly n f
  exact Nat.sInf_le h
