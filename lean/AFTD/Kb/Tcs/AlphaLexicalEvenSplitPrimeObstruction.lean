import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaElementaryCellStep

/-!
# alpha_lexical_even_split_prime_obstruction

Topic: combinatorics   Node: 6d91969c9de4

Provenance: helper lemma. Computed obstruction to a possible structural route for OP-392, arXiv:2610.24758; lexical definitions from arXiv:0810.5205, Section 2.

At degree parameter 13 there are two ordered lexical sequences of degree 12 with lexical meet (3,1). Splitting the later sequence at its even zero-based index 2 produces a nonlexical sequence, even though the prefix before the split is lexical. The witnesses are (3,2,2,3,2), (3,1,2,1,3,1,1), and (3,1,1,1,1,3,1,1). No claim of adjacency is made.
-/

instance (a b : List ℕ) : Decidable (alpha_lexical_lt a b) := by
  unfold alpha_lexical_lt
  infer_instance
instance (a : List ℕ) : Decidable (alpha_is_lexical a) := by
  unfold alpha_is_lexical
  infer_instance
instance (a b : List ℕ) (i : ℕ) : Decidable (alpha_elementary_cell_step a b i) := by
  unfold alpha_elementary_cell_step
  infer_instance

theorem alpha_lexical_even_split_prime_obstruction :
  let a : List ℕ := [3,2,2,3,2]
  let b : List ℕ := [3,1,2,1,3,1,1]
  let c : List ℕ := [3,1,1,1,1,3,1,1]
  alpha_is_lexical a ∧ alpha_is_lexical b ∧ alpha_lexical_lt a b ∧
  a.sum + 1 = 13 ∧ b.sum + 1 = 13 ∧ Nat.Prime 13 ∧
  alpha_lexical_meet a b = [3,1] ∧ alpha_is_lexical (b.take 2) ∧
  alpha_elementary_cell_step b c 2 ∧ ¬ alpha_is_lexical c := by decide
