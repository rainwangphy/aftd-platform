import AFTD.Prelude

/-!
# is_admissible_diagonal_selection

Topic: combinatorics   Node: eca6e3badca0

Provenance: formalization of a published result. Source: arXiv:2610.33042 Section 1 and Section 2

A selection M of unit diagonals on the grid V_{2k-1} = {0, ..., 2k-1}^2 is admissible if its edges are unit diagonals, have pairwise disjoint endpoints, and no unit square contains both of its diagonals.
-/

/-- An admissible selection of unit diagonals on V_{2k-1} is a matching of unit diagonals containing at most one diagonal from each unit square. -/
def is_admissible_diagonal_selection (k : ℕ) (M : Finset (Sym2 (Fin (2 * k) × Fin (2 * k)))) : Prop := (∀ e ∈ M, ∃ u v, e = s(u, v) ∧
    ((∃ (r c : ℕ) (hr : r + 1 < 2 * k) (hc : c + 1 < 2 * k),
      (u = (⟨r, by omega⟩, ⟨c, by omega⟩) ∧ v = (⟨r + 1, hr⟩, ⟨c + 1, hc⟩) ∨
       u = (⟨r + 1, hr⟩, ⟨c + 1, hc⟩) ∧ v = (⟨r, by omega⟩, ⟨c, by omega⟩))) ∨
     (∃ (r c : ℕ) (hr : r + 1 < 2 * k) (hc : c + 1 < 2 * k),
      (u = (⟨r, by omega⟩, ⟨c + 1, hc⟩) ∧ v = (⟨r + 1, hr⟩, ⟨c, by omega⟩) ∨
       u = (⟨r + 1, hr⟩, ⟨c, by omega⟩) ∧ v = (⟨r, by omega⟩, ⟨c + 1, hc⟩))))) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v, v ∈ e₁ → v ∉ e₂) ∧
  (∀ (r c : ℕ) (hr : r + 1 < 2 * k) (hc : c + 1 < 2 * k),
    ¬ (s((⟨r, by omega⟩, ⟨c, by omega⟩), (⟨r + 1, hr⟩, ⟨c + 1, hc⟩)) ∈ M ∧
       s((⟨r, by omega⟩, ⟨c + 1, hc⟩), (⟨r + 1, hr⟩, ⟨c, by omega⟩)) ∈ M))
