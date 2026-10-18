import AFTD.Prelude
import AFTD.Kb.Optimization.SymmetrizeImageMatroidPolytopeEqFixed
import AFTD.Kb.Optimization.MultilinearExtension
import AFTD.Kb.Optimization.MatroidPolytope
import AFTD.Kb.Optimization.PermGroupSymmetrize
import AFTD.Kb.Optimization.IsStronglySymmetricInstance

/-!
# symmetry_gap_numerator_eq_sSup_fixed

Topic: submodular   Node: b5ea775096a7

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

For a strongly symmetric instance the numerator of the symmetry gap, sup_{x∈P(M)} F(x̄), equals the supremum of F over the points of the matroid polytope that are fixed by the group.
-/

/-- The numerator of the symmetry gap is a supremum of F over the fixed polytope P(M) ∩ Fix(G). -/
theorem symmetry_gap_numerator_eq_sSup_fixed {m : ℕ} (M : Matroid (Fin m))
    (f : Finset (Fin m) → ℝ) (G : Subgroup (Equiv.Perm (Fin m)))
    (hs : is_strongly_symmetric_instance M f G) :
    sSup ((fun x => multilinear_extension f (perm_group_symmetrize G x)) '' matroid_polytope M)
      = sSup (multilinear_extension f ''
          (matroid_polytope M ∩ {x | perm_group_symmetrize G x = x})) := by
  rw [← Set.image_image, symmetrize_image_matroid_polytope_eq_fixed M f G hs]
