import AFTD.Prelude

/-!
# anticomplete_neighbor_defect_bound

Topic: graphs   Node: aee00822a045

Provenance: helper lemma. OP-1957: degree and incidence bounds for the size-five block route.

A vertex anticomplete to a specified block misses at most r of its allowed neighbors when its degree is within r of their total number.
-/

theorem anticomplete_neighbor_defect_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (x : V) (hx : x ∉ B)
    (hanti : ∀ b ∈ B, ¬ G.Adj x b) (d r : ℕ)
    (hsize : Fintype.card V = B.card + d + 1)
    (hdegree : d ≤ (G.neighborFinset x).card + r) :
    (((Finset.univ \ B).erase x) \ G.neighborFinset x).card ≤ r := by
  classical
  have hsub : G.neighborFinset x ⊆ (Finset.univ \ B).erase x := by
    intro y hy
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨hxy.ne.symm, fun hyB => hanti y hyB hxy⟩
  have hxmem : x ∈ (Finset.univ : Finset V) \ B := by simp [hx]
  have hbase : ((Finset.univ : Finset V) \ B).card = d+1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ]
    omega
  have hcard : ((Finset.univ \ B).erase x).card = d := by
    rw [Finset.card_erase_of_mem hxmem, hbase]
    omega
  rw [Finset.card_sdiff_of_subset hsub, hcard]
  omega
