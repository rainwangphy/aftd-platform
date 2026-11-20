import AFTD.Prelude

/-!
# op309_common_host_graph

Topic: graphs   Node: d1af00f4e5dc

Provenance: helper lemma. OP-309 overlap-aware port incidence selection, IN-1099.

The simple graph joining distinct port classes exactly when they share a host component.
-/

def op309_common_host_graph {A B : Type*} (I : SimpleGraph (A ⊕ B)) : SimpleGraph A where
  Adj a a' := a ≠ a' ∧ ∃ b : B, I.Adj (.inl a) (.inr b) ∧ I.Adj (.inl a') (.inr b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.2, h.2.choose_spec.1⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩
