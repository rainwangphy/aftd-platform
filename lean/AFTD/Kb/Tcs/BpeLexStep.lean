import AFTD.Prelude
import AFTD.Kb.Tcs.BpeLexBestPair
import AFTD.Kb.Tcs.BpeFullMerge

/-!
# bpe_lex_step

Topic: algorithms   Node: 694371d774fb

Provenance: formalization of a published result. Source: OP-1536

Performs one greedy full BPE merge step replacing the chosen lexicographically earliest maximal pair with fresh symbol z, leaving the string unchanged if no pair occurs.
-/

/-- One deterministic greedy BPE merge step replacing the chosen pair with a fresh symbol. -/
def bpe_lex_step (z : ℕ) (s : List ℕ) : List ℕ :=
  match bpe_lex_best_pair s with
  | none => s
  | some (a, b) => bpe_full_merge a b z s
