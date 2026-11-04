import AFTD.Prelude
import AFTD.Kb.Tcs.TruncatedAddCayley
import AFTD.Kb.Tcs.IsDirectSumSet
import AFTD.Kb.Tcs.TruncatedAddCayleyIndepOfIsDirectSumSet
import AFTD.Kb.Tcs.TruncatedAddCayleyExistsAdjOfNotMem

/-!
# direct_sum_cover_maximal_independent_truncated_cayley

Topic: combinatorics   Node: 5689fb361856

Provenance: formalization of a published result. Source: arXiv:2611.05321 Lemma 2.2

Let G be an additive abelian group, and let A ⊆ D ⊆ G and Z ⊆ G be subsets with 0 ∈ Z. Suppose that the sum A + Z is direct and D ⊆ A + Z. Then the preimage of A in D is a maximal independent set in the truncated Cayley graph on D with connection set Z - Z.
-/

open scoped Pointwise in
/-- Direct sum covers yield maximal independent sets in truncated Cayley graphs (Lemma 2.2). -/
theorem direct_sum_cover_maximal_independent_truncated_cayley {G : Type*} [AddCommGroup G]
    {A D Z : Set G} (hAD : A ⊆ D) (h0 : (0 : G) ∈ Z)
    (h_dir : is_direct_sum_set A Z) (h_cov : D ⊆ A + Z) :
    Maximal (truncated_add_cayley D (Z - Z)).IsIndepSet (Subtype.val ⁻¹' A) := by
  refine ⟨truncated_add_cayley_indep_of_is_direct_sum_set h_dir, fun y hy hsub x hx => ?_⟩
  by_contra hxA
  obtain ⟨a, ha, hadj⟩ := truncated_add_cayley_exists_adj_of_not_mem hAD h0 h_cov x hxA
  exact hy hx (hsub ha) hadj.ne hadj
