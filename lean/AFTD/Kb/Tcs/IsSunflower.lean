import AFTD.Prelude

/-!
# IsSunflower

Topic: combinatorics   Node: 46ae7aa4e5c3

A finite family F of finite sets is a sunflower (a delta-system) with kernel C if every member of F contains C and any two distinct members of F have intersection exactly C.
-/

/-- A finite family of finite sets is a sunflower with kernel `C` if all members contain `C` and distinct members meet exactly in `C`. -/
def IsSunflower {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) : Prop := (∀ A ∈ F, C ⊆ A) ∧ ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = C
