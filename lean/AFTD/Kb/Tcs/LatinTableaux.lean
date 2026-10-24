import AFTD.Prelude

/-!
# latin_tableaux

Topic: combinatorics   Node: 5c6159aec9a9

Provenance: formalization of a published result. Source: scout/2610-29291-counting-and-constructing-latin-tableaux.md:450

For a Young diagram μ, the set of Latin tableaux of shape μ and type μ' is the finset of fillings T from the cells of μ to natural numbers such that each entry in cell (i, j) is between 1 and the row length μ.rowLen i, and entries are distinct along each row and distinct along each column.
-/

/-- The finset of Latin tableaux of shape μ and type μ': valid cell fillings by row-length bounded natural numbers with distinct entries along each row and column. -/
def latin_tableaux (μ : YoungDiagram) : Finset (μ.cells → ℕ) := (Fintype.piFinset fun c : μ.cells => Finset.Icc 1 (μ.rowLen c.1.1)).filter fun T =>
    (∀ (c₁ c₂ : μ.cells), c₁.1.1 = c₂.1.1 → T c₁ = T c₂ → c₁.1.2 = c₂.1.2) ∧
    (∀ (c₁ c₂ : μ.cells), c₁.1.2 = c₂.1.2 → T c₁ = T c₂ → c₁.1.1 = c₂.1.1)
