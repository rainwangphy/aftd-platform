import AFTD.Prelude
import AFTD.Kb.Tcs.BpePairBetter
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_lex_best_pair

Topic: algorithms   Node: 47821ac29b48

Provenance: formalization of a published result. Source: OP-1536

Selects the adjacent pair with the largest number of nonoverlapping occurrences in the string, breaking ties by lexicographical order of integer IDs, or returns none if no pair occurs.
-/

/-- The greedy pair with maximal nonoverlapping count, broken by lexicographic order. -/
def bpe_lex_best_pair (s : List ℕ) : Option (ℕ × ℕ) :=
  match s.zip s.tail with
  | [] => none
  | p :: ps =>
    let best := ps.foldl (fun acc q => if bpe_pair_better s q acc then q else acc) p
    if bpe_pair_count best.1 best.2 s = 0 then none
    else some best
