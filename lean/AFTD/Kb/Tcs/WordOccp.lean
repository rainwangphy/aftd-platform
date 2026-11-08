import AFTD.Prelude

/-!
# word_occp

Topic: automata   Node: 9b7c85ca29b7

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

For two gap profiles of equal shape, the number of indices where the first profile's entry is strictly larger than the second's.
-/

def word_occp (gw gv : List ℕ) : ℕ := (gw.zip gv).countP (fun q => decide (q.2 < q.1))
