import AFTD.Prelude

/-!
# PreferenceWithUniqueTop

Topic: social_choice   Node: b091a539c697

Provenance: formalization of a published result. Source: scout/2611-18282-safe-manipulation-of-tops-only-voting-rules.md:215

A preference relation on alternatives with a complete and transitive weak preference relation and a unique top alternative.
-/

/-- Preference relation on alternatives with complete and transitive weak preference and a unique top alternative. -/
structure PreferenceWithUniqueTop (X : Type*) where
  rel : X → X → Prop
  total : ∀ x y, rel x y ∨ rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z
  top : X
  unique_top : ∀ y, y ≠ top → ¬ rel y top
