import AFTD.Prelude

/-!
# finite_single_outside_packing_replacement

Topic: combinatorics   Node: c32cae8ead42

Provenance: helper lemma. Simultaneous remapping step for simple_graph_triangle_packing_pair_deletion_forcing_quadratic_kernel.

Replacing each of a finite family of sets by one with a distinct fresh outside vertex preserves the size and pairwise at-most-one intersection of an existing packing, provided the inside intersections stay at most one.
-/

theorem finite_single_outside_packing_replacement
    {ι V : Type*} [Fintype ι] [DecidableEq V]
    (S : Finset V) (P : Finset (Finset V)) (T : ι → Finset V) (f : ι → V)
    (hP : (P : Set (Finset V)).Pairwise (fun q r => (q ∩ r).card ≤ 1))
    (hout : ∀ i, T i \ S = {f i})
    (hfinj : Function.Injective f)
    (hfresh : ∀ i, f i ∉ P.biUnion id)
    (hwithin : ∀ i j, i ≠ j → ((T i ∩ T j) ∩ S).card ≤ 1)
    (hbetween : ∀ q ∈ P, ∀ i, ((q ∩ T i) ∩ S).card ≤ 1) :
    (P ∪ Finset.univ.image T).card = P.card + Fintype.card ι ∧
    ((P ∪ Finset.univ.image T : Finset (Finset V)) : Set (Finset V)).Pairwise
      (fun q r => (q ∩ r).card ≤ 1) := by
  classical
  have hout_iff : ∀ i v, v ∈ T i → v ∉ S → v = f i := by
    intro i v hv hs
    have hm : v ∈ T i \ S := Finset.mem_sdiff.mpr ⟨hv,hs⟩
    rw [hout i] at hm
    simpa using hm
  have hfm : ∀ i, f i ∈ T i := by
    intro i
    have hm : f i ∈ T i \ S := by rw [hout i]; simp
    exact (Finset.mem_sdiff.mp hm).1
  have hTin : Function.Injective T := by
    intro i j heq
    have hset := congrArg (fun A : Finset V => A \ S) heq
    rw [hout i, hout j] at hset
    exact hfinj (Finset.singleton_injective hset)
  have hnotP : ∀ i, T i ∉ P := by
    intro i hi
    apply hfresh i
    exact Finset.mem_biUnion.mpr ⟨T i,hi,hfm i⟩
  have hdis : Disjoint P (Finset.univ.image T) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqim
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hqim
    exact hnotP i hq
  have hcard : (P ∪ Finset.univ.image T).card = P.card + Fintype.card ι := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hTin, Finset.card_univ]
  refine ⟨hcard, ?_⟩
  intro q hq r hr hqr
  simp only [Finset.mem_coe, Finset.mem_union] at hq hr
  rcases hq with hq | hq <;> rcases hr with hr | hr
  · exact hP hq hr hqr
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hr
    have hs : q ∩ T j ⊆ S := by
      intro v hv
      obtain ⟨hvq,hvt⟩ := Finset.mem_inter.mp hv
      by_contra hvs
      have hvf := hout_iff j v hvt hvs
      apply hfresh j
      exact Finset.mem_biUnion.mpr ⟨q,hq,hvf ▸ hvq⟩
    have heq : (q ∩ T j) ∩ S = q ∩ T j := Finset.inter_eq_left.mpr hs
    simpa [heq] using hbetween q hq j
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    have hs : r ∩ T i ⊆ S := by
      intro v hv
      obtain ⟨hvr,hvt⟩ := Finset.mem_inter.mp hv
      by_contra hvs
      have hvf := hout_iff i v hvt hvs
      apply hfresh i
      exact Finset.mem_biUnion.mpr ⟨r,hr,hvf ▸ hvr⟩
    have heq : (r ∩ T i) ∩ S = r ∩ T i := Finset.inter_eq_left.mpr hs
    have hh : (r ∩ T i).card ≤ 1 := by simpa [heq] using hbetween r hr i
    simpa [Finset.inter_comm] using hh
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hr
    have hij : i ≠ j := fun h => hqr (by rw [h])
    have hs : T i ∩ T j ⊆ S := by
      intro v hv
      obtain ⟨hvi,hvj⟩ := Finset.mem_inter.mp hv
      by_contra hvs
      have hi := hout_iff i v hvi hvs
      have hj := hout_iff j v hvj hvs
      exact hij (hfinj (hi.symm.trans hj))
    have heq : (T i ∩ T j) ∩ S = T i ∩ T j := Finset.inter_eq_left.mpr hs
    simpa [heq] using hwithin i j hij
