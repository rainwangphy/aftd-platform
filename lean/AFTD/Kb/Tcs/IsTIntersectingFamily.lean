import AFTD.Prelude

/-!
# is_t_intersecting_family

Topic: combinatorics   Node: 42ff0cdbde3f

Provenance: formalization of a published result. Source: arXiv:2611.25346 Sec. 1, line 90

Given a type α with decidable equality, a threshold t : ℕ, and a finite family ℱ : Finset (Finset α) of finite subsets of α, is_t_intersecting_family t ℱ holds if and only if for all subsets A, B ∈ ℱ, the cardinality of their intersection A ∩ B is at least t.
-/

/-- A finite family of finite sets is t-intersecting if any two sets in the family share at least t elements. -/
def is_t_intersecting_family {α : Type*} [DecidableEq α] (t : ℕ) (ℱ : Finset (Finset α)) : Prop := ∀ A ∈ ℱ, ∀ B ∈ ℱ, t ≤ (A ∩ B).card
