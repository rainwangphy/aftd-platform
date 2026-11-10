import AFTD.Prelude
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_max_pair_count

Topic: algorithms   Node: 60b634f38ab8

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

The largest nonoverlapping full-merge pair count among adjacent pairs of the current string, with maximum zero for a string shorter than two.
-/

def bpe_max_pair_count (s : List ℕ) : ℕ :=
  (s.zip s.tail).toFinset.sup (fun p => bpe_pair_count p.1 p.2 s)
