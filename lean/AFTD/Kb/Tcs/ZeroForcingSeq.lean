import AFTD.Prelude

/-!
# zero_forcing_seq

Topic: graphs   Node: 2927be495ce1

Provenance: formalization of a published result. Source: arXiv:2611.13244, Section 1 and Section 2 -- Stabilization of the zero forcing number of generalized Petersen graphs

The sequence of vertex subsets B_i in a simple graph G starting with B_0 = S and iteratively defined by adding all unique outside neighbors of vertices in B_i.
-/

/-- The sequence of vertex subsets B_i obtained by iteratively applying the zero forcing color change rule starting from S. -/
def zero_forcing_seq {V : Type*} (G : SimpleGraph V) (S : Set V) : ℕ → Set V
| 0 => S
| n + 1 => (zero_forcing_seq G S n) ∪ {w : V | ∃ x ∈ zero_forcing_seq G S n, G.neighborSet x \ zero_forcing_seq G S n = {w}}
