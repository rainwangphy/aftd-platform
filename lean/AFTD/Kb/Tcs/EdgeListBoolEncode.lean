import AFTD.Prelude

/-!
# edge_list_bool_encode

Topic: np_completeness   Node: 47282ef9fdd1

Provenance: helper lemma. Input encoding for the decision problem of arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 1 (H-coloring of connected cubic graphs): a unary edge-list encoding, polynomially equivalent to the usual binary ones

Encodes an edge list es : List (ℕ × ℕ) as a word over Bool: es.flatMap of the map sending a pair e to List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false]), i.e. each number k is written in unary as k copies of true then false, and the codes of the pairs are concatenated in order.
-/

/-- Unary encoding of an edge list as a Bool word. -/
def edge_list_bool_encode (es : List (ℕ × ℕ)) : List Bool :=
  es.flatMap (fun e => List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false]))
