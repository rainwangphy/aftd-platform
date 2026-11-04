import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphNonneighborKernelOrDominatingVertex

/-!
# digraph_nonneighborhood_kernel_neighborhood_lift

Topic: graphs   Node: 13f56a3c4794

Provenance: helper lemma. Consequence of the dominated-deletion argument in the proof of Theorem 3.4(1), https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p32/pdf/; additional literature review is needed before asserting novelty.

In a finite loopless oriented graph where the non-neighbors of every vertex admit an out-kernel, every vertex has a quasi-kernel whose closed out-neighborhood contains that vertex and all its out-neighbors.
-/

theorem digraph_nonneighborhood_kernel_neighborhood_lift
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ x, ¬ D.Adj x x)
    (horient : ∀ x y, D.Adj x y → ¬ D.Adj y x)
    (hlocal : ∀ v, ∃ K : Finset α,
      (∀ x ∈ K, x ≠ v ∧ ¬ D.Adj x v ∧ ¬ D.Adj v x) ∧
      (∀ x ∈ K, ∀ y ∈ K, x ≠ y → ¬ D.Adj x y) ∧
      (∀ x, x ≠ v → ¬ D.Adj x v → ¬ D.Adj v x →
        ∃ k ∈ K, k = x ∨ D.Adj k x)) (v : α) :
    ∃ Q : Finset α,
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ D.Adj x y) ∧
      (∀ x, ∃ q ∈ Q, q = x ∨ D.Adj q x ∨ ∃ z, D.Adj q z ∧ D.Adj z x) ∧
      (∀ x, x = v ∨ D.Adj v x → ∃ q ∈ Q, q = x ∨ D.Adj q x) := by
  classical
  let N : α → Finset α := fun t => Finset.univ.filter (fun z => D.Adj z t)
  let P : Finset α := Finset.univ.filter fun t =>
    t = v ∨ (D.Adj t v ∧ ∀ z, D.Adj z t → D.Adj z v)
  have hP : P.Nonempty := ⟨v, by simp [P]⟩
  obtain ⟨s, hsP, hmin⟩ := Finset.exists_min_image P (fun t => (N t).card) hP
  have hs : s = v ∨ (D.Adj s v ∧ ∀ z, D.Adj z s → D.Adj z v) :=
    (Finset.mem_filter.mp hsP).2
  obtain ⟨K, hK, hind, hdom⟩ := hlocal s
  rcases digraph_nonneighbor_kernel_or_dominating_vertex D s K hK hind hdom with
    ⟨hQind, hQcov⟩ | ⟨t, htsne, hts, htsub⟩
  · refine ⟨insert s K, hQind, hQcov, ?_⟩
    intro x hx
    rcases hs with rfl | ⟨hsv, hsin⟩
    · rcases hx with h | hvx
      · exact ⟨x, by simp [h], Or.inl rfl⟩
      · exact ⟨s, by simp, Or.inr hvx⟩
    · rcases hx with rfl | hvx
      · exact ⟨s, by simp, Or.inr hsv⟩
      · by_cases hxs : x = s
        · subst x
          exact ⟨s, by simp, Or.inl rfl⟩
        · by_cases hsx : D.Adj s x
          · exact ⟨s, by simp, Or.inr hsx⟩
          · have hxs' : ¬ D.Adj x s := by
              intro h
              exact (horient v x hvx) (hsin x h)
            obtain ⟨k, hk, hkx⟩ := hdom x hxs hxs' hsx
            exact ⟨k, Finset.mem_insert_of_mem hk, hkx⟩
  · have htP : t ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ t, Or.inr ⟨?_, ?_⟩⟩
      · rcases hs with rfl | ⟨_, hsin⟩
        · exact hts
        · exact hsin t hts
      · intro z hzt
        rcases hs with rfl | ⟨_, hsin⟩
        · exact htsub z hzt
        · exact hsin z (htsub z hzt)
    have hsub : N t ⊆ N s := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        htsub z (Finset.mem_filter.mp hz).2⟩
    have htsmem : t ∈ N s := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, hts⟩
    have hnotmem : t ∉ N t := by
      intro ht
      exact hloop t (Finset.mem_filter.mp ht).2
    have hproper : N t ⊂ N s := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro heq
      apply hnotmem
      simpa [heq] using htsmem
    have hlt := Finset.card_lt_card hproper
    have hle := hmin t htP
    omega
