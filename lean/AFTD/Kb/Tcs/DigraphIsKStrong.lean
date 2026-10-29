import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_is_k_strong

Topic: graphs   Node: 217a099cb928

Provenance: formalization of a published result. Source: arXiv:2610.36895 Sec. 2

A finite digraph D is k-strong (k-strongly connected) if its vertex count exceeds k and for every vertex subset s of cardinality strictly less than k and every distinct pair u, v not in s, there exists a directed path in D from u to v avoiding s.
-/

/-- A finite digraph is k-strong if deleting fewer than k vertices leaves a strongly connected digraph. -/
def digraph_is_k_strong {V : Type*} [Fintype V] (D : Digraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
  ∀ (s : Finset V), s.card < k →
    ∀ (u v : V), u ∉ s → v ∉ s → u ≠ v →
      ∃ p : List V, digraph_is_directed_path D p u v ∧ ∀ x ∈ p, x ∉ s
