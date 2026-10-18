import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtensionIndicator
import AFTD.Kb.Optimization.MatroidPolytope
import AFTD.Kb.Optimization.MultilinearExtension
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# sSup_indep_le_sSup_multilinear_extension

Topic: submodular   Node: 73e75961b991

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

The best integral value max{f(S) : S independent in M} is at most the best fractional value max_{x∈P(M)} F(x), because every independent set is a vertex of the matroid polytope.
-/

/-- The integral optimum is at most the fractional optimum over the matroid polytope. -/
theorem sSup_indep_le_sSup_multilinear_extension {m : ℕ} (M : Matroid (Fin m))
    (f : Finset (Fin m) → ℝ) :
    sSup (f '' {S : Finset (Fin m) | M.Indep ↑S})
      ≤ sSup (multilinear_extension f '' matroid_polytope M) := by
  classical
  set V : Set (Fin m → ℝ) := {x | ∃ S : Finset (Fin m), M.Indep ↑S ∧ x = finset_indicator_vec S}
    with hV
  have hVfin : V.Finite :=
    (Set.finite_range (fun S : Finset (Fin m) => finset_indicator_vec S)).subset
      (by rintro x ⟨S, -, rfl⟩; exact ⟨S, rfl⟩)
  have hPc : IsCompact (matroid_polytope M) := hVfin.isCompact_convexHull (𝕜 := ℝ)
  have hF : Continuous (multilinear_extension f) := by
    unfold multilinear_extension; fun_prop
  have hbdd : BddAbove (multilinear_extension f '' matroid_polytope M) :=
    (hPc.image hF).bddAbove
  have hne : (f '' {S : Finset (Fin m) | M.Indep ↑S}).Nonempty := by
    refine ⟨f ∅, ∅, ?_, rfl⟩
    simp [M.empty_indep]
  refine csSup_le hne ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [← multilinear_extension_indicator f S]
  refine le_csSup hbdd ?_
  refine ⟨finset_indicator_vec S, ?_, rfl⟩
  exact subset_convexHull ℝ _ ⟨S, hS, rfl⟩
