import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BitwordRotate

/-!
# alpha_lexical_example_eleven

Topic: combinatorics   Node: be3a63517acd

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

Kernel-checked encoding of the length-eleven example in arXiv:0810.5205, Example 3.2, including its one-bit completed words and the uniform rotation to forward Gray ranks.
-/

instance alpha_lexical_lt_decidable (a b : List ℕ) : Decidable (alpha_lexical_lt a b) :=
  inferInstanceAs (Decidable (∃ i < max a.length b.length,
    (∀ j < i, alpha_signed_cell a j = alpha_signed_cell b j) ∧
      alpha_signed_cell a i < alpha_signed_cell b i))

instance alpha_is_lexical_decidable (a : List ℕ) : Decidable (alpha_is_lexical a) :=
  inferInstanceAs (Decidable (a ≠ [] ∧ (∀ v ∈ a, 0 < v) ∧
    ∀ k < a.length, 0 < k → alpha_lexical_lt (a.drop k) a))

instance alpha_elementary_cell_step_decidable (a b : List ℕ) (i : ℕ) :
    Decidable (alpha_elementary_cell_step a b i) := by
  unfold alpha_elementary_cell_step
  infer_instance

theorem alpha_lexical_example_eleven :
    alpha_is_lexical [3, 2, 3, 2] ∧
    alpha_is_lexical [3, 1, 1, 3, 2] ∧
    alpha_elementary_cell_step [3, 2, 3, 2] [3, 1, 1, 3, 2] 1 ∧
    alpha_lexical_lt [3, 2, 3, 2] [3, 1, 1, 3, 2] ∧
    alpha_lexical_meet [3, 2, 3, 2] [3, 1, 1, 3, 2] = [3, 1] ∧
    alpha_binary_prefix [3, 2, 3, 2] = 594 ∧
    alpha_binary_prefix [3, 1, 1, 3, 2] = 626 ∧
    (594 : ℕ) ^^^ 626 = 2 ^ 5 ∧
    (1189 : ℕ) ^^^ 1253 = 2 ^ 6 ∧
    brgc_word 1849 = 1189 ∧ brgc_word 1862 = 1253 ∧
    bitword_rotate 11 1189 = 331 ∧ bitword_rotate 11 1253 = 459 ∧
    brgc_word 397 = 331 ∧ brgc_word 370 = 459 ∧
    (331 : ℕ) ^^^ 459 = 2 ^ 7 := by
  decide
