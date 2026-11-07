import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicHasCopy

/-!
# cyclic_ramsey_property

Topic: graphs   Node: 1641411c49bf

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 1

cyclic_ramsey_property H₁ H₂ N holds if every red/blue edge-colouring of K_N contains a red cyclic copy of H₁ or a blue cyclic copy of H₂, represented by a graph G and its complement Gᶜ.
-/

/-- The 2-colour cyclic Ramsey property for graphs on cyclically ordered vertices. -/
def cyclic_ramsey_property {m n : ℕ} (H₁ : SimpleGraph (Fin m)) (H₂ : SimpleGraph (Fin n)) (N : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), cyclic_has_copy H₁ G ∨ cyclic_has_copy H₂ Gᶜ
