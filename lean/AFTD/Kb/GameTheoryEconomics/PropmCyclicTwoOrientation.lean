import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicTwoOrientation

/-!
# propm_cyclic_two_orientation

Topic: fair_division   Node: 9e67fd447a39

For n at most 5, the cyclic orientation i -> i+1, i+2 of the complete graph covers every pair and has out-degree at most two.
-/

/-- The cyclic orientation `i → i+1, i+2 (mod n)` of `K_n` covers every pair and has out-degree at most two when `n ≤ 5`. -/
lemma propm_cyclic_two_orientation (n : ℕ) (hn : n ≤ 5) :
    (∀ a b : Fin n, a ≠ b →
      cyclic_two_orientation n a b = true ∨ cyclic_two_orientation n b a = true) ∧
    ∀ i : Fin n, (Finset.univ.filter fun j => cyclic_two_orientation n i j = true).card ≤ 2 := by
  interval_cases n <;> decide
