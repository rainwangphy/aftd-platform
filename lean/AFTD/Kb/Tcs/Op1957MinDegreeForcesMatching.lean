import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.MaximumMatchingUnmatchedIndependent
import AFTD.Kb.Tcs.MaximumMatchingForbidsOneEdgeTwoUncoveredExchange
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# op1957_min_degree_forces_matching

Topic: graphs   Node: 5ef94a58c193

Provenance: helper lemma. OP-1957: matching bound needed for independence reduction

A finite graph on at least 2k vertices with minimum degree at least k has a matching of k edges.
-/

theorem op1957_min_degree_forces_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hsize : 2*k ≤ Fintype.card V)
    (hdegree : ∀ v, k ≤ (G.neighborFinset v).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
  classical
  obtain ⟨M,hM,hMS,hmax⟩ := finite_subset_has_maximum_matching G Finset.univ
  have hlarge : k ≤ M.edgeSet.ncard := by
    by_contra hn
    let D : Finset V := M.verts.toFinset
    let U : Finset V := Finset.univ \ D
    have hDcard : D.card = 2*M.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hM).symm
    have hUcard : U.card + D.card = Fintype.card V := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      simpa [U] using h
    have hUtwo : 1 < U.card := by omega
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hUtwo
    have huM : u ∉ M.verts := by simpa [U,D] using hu
    have hvM : v ∉ M.verts := by simpa [U,D] using hv
    have hNsub : ∀ w ∈ U, G.neighborFinset w ⊆ D := by
      intro w hw a ha
      have hwM : w ∉ M.verts := by simpa [U,D] using hw
      by_contra haD
      have haM : a ∉ M.verts := by simpa [D] using haD
      exact maximum_matching_unmatched_independent G Finset.univ M hM hMS hmax
        w (Finset.mem_univ _) hwM a (Finset.mem_univ _) haM (by simpa using ha)
    let f : V → V := fun x => if hx : x ∈ M.verts then Classical.choose (hM hx) else x
    have hf : ∀ x ∈ D, M.Adj x (f x) := by
      intro x hx
      have hxM : x ∈ M.verts := by simpa [D] using hx
      simpa [f,hxM] using (Classical.choose_spec (hM hxM)).1
    have hfD : ∀ x ∈ D, f x ∈ D := by
      intro x hx
      have hh := M.edge_vert (hf x hx).symm
      simpa [D] using hh
    have hfinv : ∀ x ∈ D, f (f x) = x := by
      intro x hx
      have hfxD := hfD x hx
      exact (hM (by simpa [D] using hfxD)).unique (hf (f x) hfxD) (hf x hx).symm
    have hfinj : Set.InjOn f (D : Set V) := by
      intro x hx y hy hxy
      calc
        x = f (f x) := (hfinv x hx).symm
        _ = f (f y) := congrArg f hxy
        _ = y := hfinv y hy
    let P := (G.neighborFinset u).image f
    let Q := G.neighborFinset v
    have hPsub : P ⊆ D := by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact hfD b (hNsub u hu hb)
    have hQsub : Q ⊆ D := hNsub v hv
    have hPcard : P.card = (G.neighborFinset u).card := by
      dsimp [P]
      apply Finset.card_image_iff.mpr
      exact hfinj.mono (by intro x hx; exact hNsub u hu hx)
    have hdis : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro a ha hq
      obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha
      have hbD := hNsub u hu hb
      have hmb : M.Adj b a := by simpa [← hba] using hf b hbD
      exact maximum_matching_forbids_one_edge_two_uncovered_exchange G Finset.univ M hM hMS hmax
        u v b a (Finset.mem_univ _) (Finset.mem_univ _) huM hvM huv hmb (by simpa using hb) (by simpa [Q] using hq)
    have hbound := Finset.card_le_card (Finset.union_subset hPsub hQsub)
    rw [Finset.card_union_of_disjoint hdis,hPcard] at hbound
    have hdu := hdegree u
    have hdv := hdegree v
    dsimp [Q] at hbound
    change (G.neighborFinset u).card + (G.neighborFinset v).card ≤ D.card at hbound
    omega
  obtain ⟨N,hN,_,hNk⟩ := finite_matching_has_submatching_of_each_smaller_size G M hM k hlarge
  exact ⟨N,hN,hNk⟩
