import AFTD.Prelude
import AFTD.Kb.Tcs.BpeLexStep

/-!
# bpe_lex_run

Topic: algorithms   Node: 20f8407bb59d

Provenance: original. Related work: knowledgebase

The string obtained by performing k sequential greedy lexicographical full BPE merges on an initial string over symbols 0 and 1.
-/

/-- Performs k greedy full BPE merges with fresh symbol IDs 2, 3, ..., k + 1. -/
def bpe_lex_run : ℕ → List ℕ → List ℕ
| 0, s => s
| k + 1, s => bpe_lex_step (k + 2) (bpe_lex_run k s)
