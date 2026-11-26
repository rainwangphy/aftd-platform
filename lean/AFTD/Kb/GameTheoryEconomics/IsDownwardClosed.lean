import AFTD.Prelude

/-!
# is_downward_closed

Topic: mechanism_design   Node: 9b12469b9ced

Provenance: formalization of a published result. Source: arXiv:2611.33095 Section 2.1

A family of finite sets F : Set (Finset E) is downward-closed if for every finite set S in F, any finite subset T of S also belongs to F.
-/

/-- A family of finite sets F is downward closed if every finite subset of an element of F is also in F. -/
def is_downward_closed {E : Type*} (F : Set (Finset E)) : Prop := ∀ ⦃S T : Finset E⦄, S ∈ F → T ⊆ S → T ∈ F
