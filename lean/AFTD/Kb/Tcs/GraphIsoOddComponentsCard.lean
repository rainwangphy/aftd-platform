import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# graph_iso_odd_components_card

Topic: graphs   Node: 053c77659107

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A finite graph isomorphism preserves the number of odd connected components.
-/

theorem graph_iso_odd_components_card
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    G.oddComponents.ncard = H.oddComponents.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    let f := e.connectedComponentEquiv
    have hf : ∀ c : G.ConnectedComponent, c ∈ G.oddComponents ↔ f c ∈ H.oddComponents := by
      intro c
      have hc : c.supp.ncard = (f c).supp.ncard := by
        rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
        exact Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp e c)
      change Odd c.supp.ncard ↔ Odd (f c).supp.ncard
      rw [hc]
    have himage : f '' G.oddComponents = H.oddComponents := by
      ext c
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (hf x).mp hx
      · intro hc
        refine ⟨f.symm c,?_,by simp⟩
        apply (hf (f.symm c)).mpr
        simpa using hc
    rw [← himage,Set.ncard_image_of_injective _ f.injective]
