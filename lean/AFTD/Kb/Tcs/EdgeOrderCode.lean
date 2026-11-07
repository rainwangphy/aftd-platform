import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode

/-!
# edge_order_code

Topic: approximation   Node: bfcd2c54d72f

Provenance: helper lemma. Output encoding for the polynomial-time statement of OP-851 (arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 8, open question (1)).

The binary encoding of a querying order (a list of edges of a graph on vertices 0..n-1): the edges in order, each edge {i, j} written as its smaller endpoint followed by its larger endpoint, each in the self-delimiting code nat_self_delimiting_code.
-/

def edge_order_code {n : ℕ} {G : SimpleGraph (Fin n)} (π : List G.edgeSet) : List Bool :=
  π.flatMap fun e => Sym2.lift ⟨fun a b : Fin n =>
    nat_self_delimiting_code (min a b : Fin n) ++ nat_self_delimiting_code (max a b : Fin n),
    fun a b => by dsimp only; rw [min_comm, max_comm]⟩ e.1
