import AFTD.Prelude
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_pair_better

Topic: algorithms   Node: b36570390996

Provenance: formalization of a published result. Source: OP-1536

Comparison between two symbol pairs in a string, preferring the pair with strictly more nonoverlapping occurrences, and breaking ties by lexicographic order on pair IDs.
-/

/-- Boolean comparison favoring higher nonoverlapping count, breaking ties lexicographically. -/
def bpe_pair_better (s : List ℕ) (p q : ℕ × ℕ) : Bool :=
  let cp := bpe_pair_count p.1 p.2 s
  let cq := bpe_pair_count q.1 q.2 s
  if cp > cq then true
  else if cp < cq then false
  else if p.1 < q.1 then true
  else if p.1 > q.1 then false
  else p.2 < q.2
