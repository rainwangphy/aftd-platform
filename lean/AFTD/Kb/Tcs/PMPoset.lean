import AFTD.Prelude

/-!
# PMPoset

Topic: algorithms   Node: 4e8ad7cee435

A strict partial order on the ground set Fin n, given by a Boolean relation lt (lt a b = true means a ≺ b).
-/

/-- A strict partial order on the ground set `Fin n`, given by a Boolean relation `lt` (`lt a b = true` means `a ≺ b`). -/
structure PMPoset (n : ℕ) where
  lt : Fin n → Fin n → Bool
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
