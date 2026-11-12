import AFTD.Prelude

/-!
# is_recurrent_word

Topic: combinatorics   Node: afedc9e37f46

Provenance: formalization of a published result. Source: arXiv:2611.13676 Section 2

An infinite word w is recurrent if every factor of w occurs at least twice in w.
-/

/-- An infinite word is recurrent if every factor that occurs in it has at least two occurrences. -/
def is_recurrent_word {α : Type*} (w : ℕ → α) : Prop := ∀ u : List α, (∃ i : ℕ, u = (List.range u.length).map (fun j => w (i + j))) →
  ∃ i j : ℕ, i < j ∧ u = (List.range u.length).map (fun m => w (i + m)) ∧
    u = (List.range u.length).map (fun m => w (j + m))
