import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# indexed_disjoint_cross_edges_form_matching

Topic: graphs   Node: 421fff2d5115

Provenance: helper lemma. Indexed matching construction for OP-1957; https://arxiv.org/abs/2611.22690.

Injectively indexed edges with disjoint endpoint ranges form a matching of the expected size.
-/

theorem indexed_disjoint_cross_edges_form_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ)
    (f g : Fin r → V) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : ∀ i j, f i ≠ g j) (hadj : ∀ i, G.Adj (f i) (g i)) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.edgeSet.ncard = r ∧
      N.verts = Set.range f ∪ Set.range g := by
  classical
  let A : Set V := Set.range f
  let B : Set V := Set.range g
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i,rfl⟩ ⟨j,hj⟩
    exact hdis i j hj.symm
  let ef : Fin r ≃ A := Equiv.ofInjective f hf
  let eg : Fin r ≃ B := Equiv.ofInjective g hg
  let e : A ≃ B := ef.symm.trans eg
  have he : ∀ v : A, G.Adj v (e v) := by
    intro v
    have hfv : f (ef.symm v) = v.val := Equiv.apply_ofInjective_symm hf v
    have hgv : (e v).val = g (ef.symm v) := by
      rfl
    rw [← hfv,hgv]
    exact hadj (ef.symm v)
  obtain ⟨N,hverts,hN⟩ := SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hAB e he
  refine ⟨N,hN,?_,hverts⟩
  have hn := in1076_matching_twice_card hN
  have hA : A.ncard = r := by simpa [A] using Set.ncard_range_of_injective hf
  have hB : B.ncard = r := by simpa [B] using Set.ncard_range_of_injective hg
  rw [hverts, Set.ncard_union_eq hAB, hA, hB] at hn
  omega
