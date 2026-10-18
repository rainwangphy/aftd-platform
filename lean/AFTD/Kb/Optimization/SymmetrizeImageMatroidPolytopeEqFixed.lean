import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrizeIdempotent
import AFTD.Kb.Optimization.PermGroupSymmetrizeMemMatroidPolytope
import AFTD.Kb.Optimization.MatroidPolytope
import AFTD.Kb.Optimization.IsStronglySymmetricInstance
import AFTD.Kb.Optimization.PermGroupSymmetrize

/-!
# symmetrize_image_matroid_polytope_eq_fixed

Topic: submodular   Node: d3af5be86ae2

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

For a strongly symmetric instance, the image of the matroid polytope under symmetrization is exactly the set of points of the polytope fixed by every element of G.
-/

/-- The symmetrized matroid polytope is exactly the part of the polytope fixed by the group. -/
theorem symmetrize_image_matroid_polytope_eq_fixed {m : ℕ} (M : Matroid (Fin m))
    (f : Finset (Fin m) → ℝ) (G : Subgroup (Equiv.Perm (Fin m)))
    (hs : is_strongly_symmetric_instance M f G) :
    (fun x => perm_group_symmetrize G x) '' matroid_polytope M
      = matroid_polytope M ∩ {x | perm_group_symmetrize G x = x} := by
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨perm_group_symmetrize_mem_matroid_polytope M f G hs hy, perm_group_symmetrize_idempotent G y⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨x, hx, hfix⟩
