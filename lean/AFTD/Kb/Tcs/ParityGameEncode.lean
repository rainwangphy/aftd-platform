import AFTD.Prelude

/-!
# parity_game_encode

Topic: automata   Node: cdc1bf362fd3

Provenance: original. Related work: Encoding chosen here for stating OP-37 (parity games in polynomial time); unary numbers and the adjacency matrix, of length polynomial in |V| + |E| when priorities are at most |V|.

For a natural number n, an owner map own : Fin n → Bool, a priority map prio : Fin n → ℕ, an edge relation E : Fin n → Fin n → Bool and a vertex v : Fin n (arguments in this order: n, own, prio, E, v), parity_game_encode n own prio E v is the list of Booleans obtained by concatenating: n copies of true followed by one false; then v copies of true (v as a number) followed by one false; then, for each vertex u = 0, 1, ..., n−1 in increasing order, the block consisting of the bit own u, then prio u copies of true followed by one false, then the n bits E u 0, E u 1, ..., E u (n−1).
-/

/-- A binary encoding of a parity game on `Fin n` with a start vertex: `n` in unary, the start vertex in unary, then for each vertex its owner bit, its priority in unary and its row of the adjacency matrix. Its length is polynomial in the number of vertices and edges when priorities are at most `n`. -/
def parity_game_encode (n : ℕ) (own : Fin n → Bool) (prio : Fin n → ℕ) (E : Fin n → Fin n → Bool)
    (v : Fin n) : List Bool :=
  List.replicate n true ++ [false] ++ (List.replicate v.val true ++ [false]) ++
    (List.finRange n).flatMap (fun u =>
      [own u] ++ (List.replicate (prio u) true ++ [false]) ++ (List.finRange n).map (fun w => E u w))
