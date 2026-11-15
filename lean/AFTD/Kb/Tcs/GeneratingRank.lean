import AFTD.Prelude

/-!
# generatingRank

Topic: approximation   Node: 38603605a367

Provenance: formalization of a published result. Source: arXiv:2611.15074 Definition 2.5

The generating rank rk(X) of a finite set of words X is the minimum cardinality of a generating set Y such that X is contained in the Kleene star of Y.
-/

/-- The generating rank of a finite set of words X over an alphabet α is the minimum cardinality of a set Y such that every word in X is formed by concatenating words from Y. -/
noncomputable def generatingRank {α : Type*} (X : Finset (List α)) : ℕ := sInf { n : ℕ | ∃ Y : Finset (List α), Y.card = n ∧ ∀ w ∈ X, ∃ L : List (List α), w = L.flatten ∧ ∀ y ∈ L, y ∈ Y }
