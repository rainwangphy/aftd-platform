import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell

/-!
# alpha_lexical_lt_irrefl

Topic: combinatorics   Node: ab50ef05e893

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The alternating lexical order is irreflexive.
-/

theorem alpha_lexical_lt_irrefl (a : List ℕ) : ¬ alpha_lexical_lt a a := by
  rintro ⟨i, hi, hagree, hlt⟩
  omega
