import AFTD.Prelude

/-!
# op_1355_independent_triple_partition_lower_bound

Topic: statistical_mechanics   Node: 213eaeeb2b5a

Provenance: helper lemma. OP-1355, explicit induced-claw witness for necessity

If three distinct pairwise nonadjacent vertices have activity 10 and every activity is nonnegative, the hard-core partition function is at least 1331.
-/

open scoped Classical BigOperators in
theorem op_1355_independent_triple_partition_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V)
    (hdist : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (hnon : ¬ G.Adj u v ∧ ¬ G.Adj u w ∧ ¬ G.Adj v w)
    (lam : V → ℝ) (hpos : ∀ x, 0 ≤ lam x)
    (hleaves : lam u = 10 ∧ lam v = 10 ∧ lam w = 10) :
    (1331 : ℝ) ≤ ∑ I ∈ (Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)), ∏ x ∈ I, lam x := by
  classical
  let L : Finset V := {u,v,w}
  have hL : G.IsIndepSet (L : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, L, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp_all [G.adj_comm]
  let F : Finset (Finset V) := Finset.univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)
  have hsub : L.powerset ⊆ F := by
    intro I hI
    have hIL : I ⊆ L := Finset.mem_powerset.mp hI
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hL.mono (by exact_mod_cast hIL)⟩
  have hn (I : Finset V) : 0 ≤ ∏ x ∈ I, lam x := by
    exact Finset.prod_nonneg fun x hx => hpos x
  have hweight : (∑ I ∈ L.powerset, ∏ x ∈ I, lam x) = 1331 := by
    rw [← Finset.prod_one_add]
    simp [L, hdist.1, hdist.2.1, hdist.2.2, hdist.1.symm, hdist.2.1.symm, hdist.2.2.symm, hleaves.1, hleaves.2.1, hleaves.2.2]
    <;> norm_num
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => hn I)
  change (1331 : ℝ) ≤ ∑ I ∈ F, ∏ x ∈ I, lam x
  linarith
