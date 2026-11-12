import AFTD.Prelude

/-!
# is_uniformly_recurrent_word

Topic: combinatorics   Node: 4ebecd4973b7

Provenance: formalization of a published result. Source: arXiv:2611.13676 Sec. 2

An infinite word w : ℕ → α is uniformly recurrent if for every finite factor u of w, there exists a bound N such that every window of length N + |u| in w contains an occurrence of u.
-/

/-- An infinite word is uniformly recurrent if every factor appears with bounded gaps between consecutive occurrences. -/
def is_uniformly_recurrent_word {α : Type*} (w : ℕ → α) : Prop := ∀ u : List α, (∃ i : ℕ, u = (List.range u.length).map (fun j => w (i + j))) →
  ∃ N : ℕ, ∀ k : ℕ, ∃ j : ℕ, k ≤ j ∧ j ≤ k + N ∧ u = (List.range u.length).map (fun m => w (j + m))
