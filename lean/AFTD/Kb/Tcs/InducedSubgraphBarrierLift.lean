import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsoOddComponentsCard

/-!
# induced_subgraph_barrier_lift

Topic: graphs   Node: 52011815784e

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A barrier in an induced graph maps to an ambient barrier of the same size, preserving the odd-component count after deletion.
-/

theorem induced_subgraph_barrier_lift
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Finset V)
    (Y : Finset {v : V | v ∈ R}) :
    ∃ X : Finset V, X ⊆ R ∧ X.card = Y.card ∧
      ((G.induce {v | v ∈ R}).induce {v | v ∉ Y}).oddComponents.ncard =
        (G.induce {v | v ∈ R ∧ v ∉ X}).oddComponents.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    let X : Finset V := Y.image Subtype.val
    have hXsub : X ⊆ R := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact w.property
    have hXcard : X.card = Y.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hmem : ∀ z : {v : V | v ∈ R}, z ∈ Y ↔ z.val ∈ X := by
      intro z
      constructor
      · intro hz
        exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
      · intro hz
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
        have he' : w=z := Subtype.ext he
        simpa [he'] using hw
    let e : ((G.induce {v | v ∈ R}).induce {v | v ∉ Y}) ≃g
        (G.induce {v | v ∈ R ∧ v ∉ X}) := {
      toFun := fun z => ⟨z.val.val,⟨z.val.property,fun hx => z.property ((hmem z.val).2 hx)⟩⟩
      invFun := fun z => ⟨⟨z.val,z.property.1⟩,fun hy => z.property.2 ((hmem ⟨z.val,z.property.1⟩).1 hy)⟩
      left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl
      map_rel_iff' := by intro u v; rfl }
    exact ⟨X,hXsub,hXcard,graph_iso_odd_components_card _ _ e⟩
