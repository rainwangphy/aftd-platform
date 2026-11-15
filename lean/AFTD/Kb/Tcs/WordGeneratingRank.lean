import AFTD.Prelude

/-!
# word_generating_rank

Topic: approximation   Node: b400b9b89d55

Provenance: formalization of a published result. Source: arXiv:2611.15074 Definition 2.5

The generating rank rk(X) of a finite set of words X over an alphabet α is the minimum cardinality of a generating set Y ⊆ α* such that every word in X can be formed by concatenating words from Y.
-/

/-- The generating rank rk(X) of a finite set of words X is the minimum cardinality of a generating set Y such that X ⊆ Y*. -/
noncomputable def word_generating_rank {α : Type*} (X : Finset (List α)) : ℕ :=
  sInf {k : ℕ | ∃ Y : Finset (List α), Y.card = k ∧ ∀ w ∈ X, ∃ L : List (List α), w = L.flatten ∧ ∀ y ∈ L, y ∈ Y}
