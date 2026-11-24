import AFTD.Prelude

/-!
# is_envy_free_outcome

Topic: social_choice   Node: 0d21fd0adb8d

Provenance: formalization of a published result. Source: arXiv:2610.24217, Section 2.2

For n parties indexed by Fin n with vote shares p : Fin n → ℝ and house size h : ℕ, an extra-seat subset S ⊆ Fin n is envy-free if for all parties i, j ∈ Fin n with p j < p i, the seats Nat.floor (h * p j) + (if j ∈ S then 1 else 0) awarded to j are at most Nat.floor (h * p i) + (if i ∈ S then 1 else 0) awarded to i.
-/

open Classical in
/-- An outcome S of extra seats is envy-free for vote shares p at house size h: a party with strictly greater vote share never receives strictly fewer seats. -/
def is_envy_free_outcome {n : ℕ} (p : Fin n → ℝ) (h : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, p j < p i →
    Nat.floor (h * p j) + (if j ∈ S then 1 else 0) ≤
    Nat.floor (h * p i) + (if i ∈ S then 1 else 0)
