import AFTD.Prelude

/-!
# op309_component_host_clique_graph

Topic: graphs   Node: 3171c7a826ba

Provenance: helper lemma. OP-309 overlap-aware port incidence selection, IN-1099.

The simple graph joining distinct class vertices exactly when they share a host vertex.
-/

def op309_component_host_clique_graph{A B : Type*} (I : SimpleGraph (A ⊕ B)) : SimpleGraph A :=
  { Adj := fun a a' => a ≠ a' ∧ ∃ b : B, I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.2, h.2.choose_spec.1⟩⟩
    loopless := ⟨fun a h => h.1 rfl⟩ }
