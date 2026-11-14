import AFTD.Prelude

/-!
# critical_three_canonical_diagonal_coverage

Topic: combinatorics   Node: 4f9cea5296c2

Provenance: helper lemma. Explicit finite certificate for OP-1112, experiment 26817.

For each pair of listed four-bit masks with sorted two-bit signatures in each of the designated chore groups, one of seven explicitly listed pairs of diagonal triples contains at most one high chore per agent.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem critical_three_canonical_diagonal_coverage :
    let bit : ℕ → ℕ → ℕ := fun x j => x / 2^j % 2
    let pop : ℕ → ℕ := fun x => bit x 0 + bit x 1 + bit x 2 + bit x 3 + bit x 4 + bit x 5 + bit x 6
    let masks : Fin 35 → ℕ := ![15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58, 60, 71, 75, 77, 78, 83, 85, 86, 89, 90, 92, 99, 101, 102, 105, 106, 108, 113, 114, 116, 120]
    let sig : ℕ → ℕ → ℕ → ℕ := fun a b j => bit a j + 2 * bit b j
    let one : ℕ → ℕ → ℕ → ℕ → Prop := fun a x y z => bit a x + bit a y + bit a z ≤ 1
    ∀ a b : Fin 35,
      (pop (masks a) = 4 ∧ pop (masks b) = 4 ∧
       sig (masks a) (masks b) 0 ≤ sig (masks a) (masks b) 1 ∧
       sig (masks a) (masks b) 1 ≤ sig (masks a) (masks b) 2 ∧
       sig (masks a) (masks b) 2 ≤ sig (masks a) (masks b) 3 ∧
       sig (masks a) (masks b) 4 ≤ sig (masks a) (masks b) 5 ∧
       sig (masks a) (masks b) 5 ≤ sig (masks a) (masks b) 6) →
      ((one (masks a) 0 1 4 ∧ one (masks b) 0 2 3) ∨
       (one (masks a) 0 4 5 ∧ one (masks b) 0 2 5) ∨
       (one (masks a) 0 2 5 ∧ one (masks b) 1 4 5) ∨
       (one (masks a) 1 4 5 ∧ one (masks b) 1 4 5) ∨
       (one (masks a) 1 2 5 ∧ one (masks b) 0 3 5) ∨
       (one (masks a) 0 2 4 ∧ one (masks b) 0 1 4) ∨
       (one (masks a) 0 2 6 ∧ one (masks b) 0 4 6)) := by
  dsimp only
  decide
