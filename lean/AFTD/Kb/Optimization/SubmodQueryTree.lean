import AFTD.Prelude

/-!
# SubmodQueryTree

Topic: submodular   Node: 7bd75ae9f6ef

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.5

An adaptive deterministic query decision tree of depth at most d for testing functions on the Boolean hypercube into {0, ..., k}.
-/

/-- A deterministic query decision tree of depth at most d for testing functions on the Boolean hypercube. -/
inductive SubmodQueryTree (n k : ℕ) : ℕ → Type where
  | leaf (accept : Bool) {d : ℕ} : SubmodQueryTree n k d
  | query {d : ℕ} (x : Fin n → Bool) (next : Fin (k + 1) → SubmodQueryTree n k d) :
      SubmodQueryTree n k (d + 1)
