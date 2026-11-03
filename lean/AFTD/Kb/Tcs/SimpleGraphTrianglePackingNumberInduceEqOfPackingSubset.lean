import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberInduceLe

/-!
# simple_graph_triangle_packing_number_induce_eq_of_packing_subset

Topic: graphs   Node: 75078ca95050

Provenance: helper lemma. step towards simple_graph_triangle_packing_cover_bounded_induced_kernel

If a subset S contains all vertices of a maximum packing of triangles in G, then the triangle packing number of the induced subgraph G[S] equals that of G.
-/

theorem simple_graph_triangle_packing_number_induce_eq_of_packing_subset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (T : Finset (Finset V)) (hT : ∀ t ∈ T, G.IsNClique 3 t)
    (hTp : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (hTc : T.card = simple_graph_triangle_packing_number G)
    (hsub : ∀ t ∈ T, ∀ x ∈ t, x ∈ S) :
    simple_graph_triangle_packing_number (G.induce (S : Set V)) =
      simple_graph_triangle_packing_number G := by
  classical
  let f : Finset V → Finset S := fun t => t.subtype (fun x => x ∈ S)
  let emb : S ↪ V := Function.Embedding.subtype (fun x => x ∈ S)
  let U := T.image f
  have hmap : ∀ t ∈ T, (f t).map emb = t := by
    intro t ht
    exact Finset.subtype_map_of_mem (hsub t ht)
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    have heq := congrArg (fun t : Finset S => t.map emb) hab
    rw [hmap a ha, hmap b hb] at heq
    exact heq
  have hcard : U.card = T.card := Finset.card_image_iff.mpr hinj
  have hc : ∀ t ∈ U, (G.induce (S : Set V)).IsNClique 3 t := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    apply (G.isNClique_induce_iff (S : Set V) (f s) 3).mpr
    change G.IsNClique 3 ((f s).map emb)
    rw [hmap s hs]
    exact hT s hs
  have hp : (U : Set (Finset S)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
    intro s hs t ht hne
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    have hne' : s' ≠ t' := by intro h; exact hne (congrArg f h)
    have h := hTp hs' ht' hne'
    have hi : ((f s' ∩ f t').map emb).card = (s' ∩ t').card := by
      rw [Finset.map_inter, hmap s' hs', hmap t' ht']
    simpa using hi.trans_le h
  have hl : T.card ≤ simple_graph_triangle_packing_number (G.induce (S : Set V)) := by
    unfold simple_graph_triangle_packing_number
    apply le_csSup
    · refine ⟨Fintype.card (Finset S), ?_⟩
      rintro n ⟨P, _, _, rfl⟩
      exact Finset.card_le_univ P
    · exact ⟨U, hc, hp, hcard⟩
  apply le_antisymm (simple_graph_triangle_packing_number_induce_le G S)
  simpa [hTc] using hl
