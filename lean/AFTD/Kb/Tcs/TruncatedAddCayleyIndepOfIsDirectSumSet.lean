import AFTD.Prelude
import AFTD.Kb.Tcs.TruncatedAddCayley
import AFTD.Kb.Tcs.IsDirectSumSet

/-!
# truncated_add_cayley_indep_of_is_direct_sum_set

Topic: combinatorics   Node: 2e120ef62adb

Provenance: helper lemma. arXiv:2611.05321 Lemma 2.2

If A and Z are subsets of an additive abelian group G whose sum A + Z is direct, then the preimage of A in D is an independent set in the truncated Cayley graph on D with connection set Z - Z.
-/

open scoped Pointwise in
/-- A direct sum component forms an independent set in the truncated Cayley graph with connection set Z - Z. -/
theorem truncated_add_cayley_indep_of_is_direct_sum_set {G : Type*} [AddCommGroup G]
    {A D Z : Set G} (h_dir : is_direct_sum_set A Z) :
    (truncated_add_cayley D (Z - Z)).IsIndepSet (Subtype.val ⁻¹' A) := by
  intro u hu v hv huv
  rintro ⟨-, h | h⟩
  · obtain ⟨g, hg, hguv⟩ := h
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_sub.mp hg
    have h' : u.val + z₁ = v.val + z₂ := by
      rw [← sub_eq_iff_eq_add, add_sub_assoc]
      exact hguv
    exact huv (Subtype.ext (h_dir u.val hu z₁ hz₁ v.val hv z₂ hz₂ h').1)
  · obtain ⟨g, hg, hgvu⟩ := h
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_sub.mp hg
    have h' : v.val + z₁ = u.val + z₂ := by
      rw [← sub_eq_iff_eq_add, add_sub_assoc]
      exact hgvu
    exact huv (Subtype.ext (h_dir v.val hv z₁ hz₁ u.val hu z₂ hz₂ h').1).symm
