import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# induced_matching_lifts

Topic: graphs   Node: 68cdae023238

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A matching of an induced graph lifts to an ambient matching supported in the inducing set with the same size.
-/

theorem induced_matching_lifts
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V)
    (M : (G.induce R).Subgraph) (hM : M.IsMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts ⊆ R ∧ N.edgeSet.ncard = M.edgeSet.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    let f : (G.induce R) →g G :=
      { toFun := Subtype.val, map_rel' := by intro a b h; exact h }
    have hf : Function.Injective f := Subtype.val_injective
    let N := M.map f
    have hN : N.IsMatching := hM.map f hf
    have hsub : N.verts ⊆ R := by
      rw [SimpleGraph.Subgraph.map_verts]
      rintro x ⟨y,hy,rfl⟩
      exact y.property
    have hverts : N.verts.ncard = M.verts.ncard := by
      rw [SimpleGraph.Subgraph.map_verts]
      exact Set.ncard_image_of_injective M.verts hf
    have h1 := in1076_matching_twice_card hN
    have h2 := in1076_matching_twice_card hM
    rw [hverts,← h2] at h1
    refine ⟨N,hN,hsub,?_⟩
    omega
