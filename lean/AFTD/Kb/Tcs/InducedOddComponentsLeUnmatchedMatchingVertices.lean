import AFTD.Prelude
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# induced_odd_components_le_unmatched_matching_vertices

Topic: graphs   Node: 30ae7f001a44

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

Each odd component of an induced graph contains a vertex missed by any matching contained in that induced graph.
-/

theorem induced_odd_components_le_unmatched_matching_vertices
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (R : Finset V) (M : G.Subgraph) [DecidablePred (· ∈ M.verts)]
    (hM : M.IsMatching) (hMR : M.verts ⊆ (R : Set V)) :
    (G.induce {v | v ∈ R}).oddComponents.ncard ≤ (R \ M.verts.toFinset).card := by
  set_option maxHeartbeats 4000000 in
    classical
    let H := G.induce {v | v ∈ R}
    let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let F : O → Finset V := fun c => in1206_component_vertices G (R : Set V) c.val
    have hFsub : ∀ c : O, F c ⊆ R := by
      intro c x hx
      exact (induced_component_ambient_vertex_properties G (R : Set V) c.val c.val).1 hx
    have hFodd : ∀ c : O, Odd (F c).card := by
      intro c
      have hh := (induced_component_ambient_vertex_properties G (R : Set V) c.val c.val).2.1
      change Odd (in1206_component_vertices G (R : Set V) c.val).card
      rw [hh]
      have hc : c.val ∈ H.oddComponents := by simpa [O] using c.property
      exact hc
    have hFmiss : ∀ c : O, ∃ x ∈ F c, x ∉ M.verts := by
      intro c
      by_contra hn
      push Not at hn
      let Q : G.Subgraph := M.induce (F c : Set V)
      have hQ : Q.IsMatching := by
        intro x hx
        have hxF : x ∈ F c := hx
        have hxM : x ∈ M.verts := hn x hxF
        obtain ⟨y,hxy,huniq⟩ := hM hxM
        have hyR : y ∈ R := hMR (M.edge_vert hxy.symm)
        have hyF : y ∈ F c := by
          by_contra hyF
          exact (induced_component_ambient_vertex_properties G (R : Set V) c.val c.val).2.2.2
            x hxF y hyR hyF (M.adj_sub hxy)
        refine ⟨y,⟨hxF,hyF,hxy⟩,?_⟩
        intro z hz
        exact huniq z hz.2.2
      have hQverts : Q.verts = (F c : Set V) := rfl
      have hc := in1076_matching_twice_card hQ
      rw [hQverts,Set.ncard_coe_finset] at hc
      obtain ⟨z,hz⟩ := hFodd c
      omega
    let pick : O → V := fun c => (hFmiss c).choose
    have hpick : ∀ c : O, pick c ∈ F c ∧ pick c ∉ M.verts := fun c => (hFmiss c).choose_spec
    have hinj : Function.Injective pick := by
      intro c d h
      apply Subtype.ext
      by_contra hne
      have hdis := (induced_component_ambient_vertex_properties G (R : Set V) c.val d.val).2.2.1 hne
      have hc := (hpick c).1
      have hd := (hpick d).1
      have he : pick c ∈ F d := by simpa [h] using hd
      exact Finset.disjoint_left.mp hdis hc he
    let T : Finset V := Finset.univ.image pick
    have hTcard : T.card = H.oddComponents.ncard := by
      dsimp [T]
      rw [Finset.card_image_of_injective _ hinj]
      change O.attach.card = H.oddComponents.ncard
      rw [Finset.card_attach]
      exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
    have hTsub : T ⊆ R \ M.verts.toFinset := by
      intro x hx
      obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_sdiff.mpr ⟨hFsub c (hpick c).1,by simpa using (hpick c).2⟩
    have hh := Finset.card_le_card hTsub
    change H.oddComponents.ncard ≤ (R \ M.verts.toFinset).card
    omega
