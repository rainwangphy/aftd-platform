import AFTD.Prelude
import AFTD.Kb.Tcs.TruncatedAddCayley

/-!
# truncated_add_cayley_exists_adj_of_not_mem

Topic: combinatorics   Node: 1652a9c22035

Provenance: helper lemma. arXiv:2611.05321 Lemma 2.2

Let A ⊆ D and Z be subsets of an additive abelian group G such that 0 ∈ Z and D ⊆ A + Z. Then every vertex of D not belonging to A is adjacent to some vertex in A in the truncated Cayley graph on D with connection set Z - Z.
-/

open scoped Pointwise in
/-- Every vertex outside A in D has a neighbor in A in the truncated Cayley graph with connection set Z - Z. -/
theorem truncated_add_cayley_exists_adj_of_not_mem {G : Type*} [AddCommGroup G]
    {A D Z : Set G} (hAD : A ⊆ D) (h0 : (0 : G) ∈ Z) (h_cov : D ⊆ A + Z)
    (x : D) (hx : x ∉ (Subtype.val ⁻¹' A : Set D)) :
    ∃ a : D, a ∈ (Subtype.val ⁻¹' A : Set D) ∧ (truncated_add_cayley D (Z - Z)).Adj x a := by
  have hx_cov : x.val ∈ A + Z := h_cov x.prop
  rcases Set.mem_add.mp hx_cov with ⟨a_val, ha, z, hz, hx_eq⟩
  have haD : a_val ∈ D := hAD ha
  let a : D := ⟨a_val, haD⟩
  use a
  refine ⟨ha, ?_⟩
  rw [truncated_add_cayley, SimpleGraph.induce_adj, SimpleGraph.addCayley_adj]
  refine ⟨?_, Or.inr ?_⟩
  · intro h_eq
    apply hx
    change x.val ∈ A
    rw [h_eq]
    exact ha
  · have : -a.val + x.val = z := by
      rw [← hx_eq]
      change -a_val + (a_val + z) = z
      abel
    rw [this, ← sub_zero z]
    exact Set.sub_mem_sub hz h0
