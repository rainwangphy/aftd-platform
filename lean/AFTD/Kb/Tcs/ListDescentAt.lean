import AFTD.Prelude

/-!
# list_descent_at

Topic: combinatorics   Node: d27c317c7550

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 4.1

A list of cells $l$ has a row descent at index $k$ (`list_descent_at l k`) if there exist cells $u$ and $v$ such that $l[k]? = some u$, $l[k+1]? = some v$, and $u.1 < v.1$ (the element at index $k$ has strictly smaller row index than the element at index $k+1$).
-/

/-- A list of cells has a row descent at index k if the cell at index k + 1 lies strictly below the cell at index k. -/
def list_descent_at (l : List (ℕ × ℕ)) (k : ℕ) : Prop := ∃ (u v : ℕ × ℕ), l[k]? = some u ∧ l[k + 1]? = some v ∧ u.1 < v.1
