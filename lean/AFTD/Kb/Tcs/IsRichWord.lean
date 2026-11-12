import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompleteReturnWord

/-!
# is_rich_word

Topic: combinatorics   Node: 31b71a4a7bdc

Provenance: formalization of a published result. Source: arXiv:2611.13676 Theorem 2.1

An infinite word w is rich in palindromes if every complete return word to a palindromic factor of w is itself a palindrome.
-/

/-- An infinite word is rich if every complete return word to any of its palindromic factors is a palindrome. -/
def is_rich_word {α : Type*} (w : ℕ → α) : Prop := ∀ c q : List α, q.Palindrome → is_complete_return_word c q →
  (∃ i : ℕ, c = (List.range c.length).map (fun j => w (i + j))) → c.Palindrome
