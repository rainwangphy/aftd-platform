import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# stochastic_mst_instance_code

Topic: approximation   Node: 976d88f30ca6

Provenance: helper lemma. Input encoding for the polynomial-time statement of OP-851 (arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 8, open question (1)); a standard adjacency-matrix encoding with binary rationals, polynomially equivalent to any standard encoding of the instance.

The binary encoding of an instance (G, p) of stochastic MST identification, G a simple graph on vertices 0..n-1 and p a rational probability on each edge: n in unary (n bits true, then false); then the upper triangle of the adjacency matrix, one bit per pair i < j in lexicographic order; then, for each edge {i, j} with i < j in the same order, the numerator (as a natural number) and the denominator of p({i, j}) in lowest terms, each in the self-delimiting code nat_self_delimiting_code.
-/

def stochastic_mst_instance_code (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : G.edgeSet → ℚ) : List Bool :=
  List.replicate n true ++ [false] ++
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
     if i < j then [decide (G.Adj i j)] else []) ++
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
     if h : i < j ∧ G.Adj i j then
       nat_self_delimiting_code (p ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h.2⟩).num.toNat ++
       nat_self_delimiting_code (p ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr h.2⟩).den
     else [])
