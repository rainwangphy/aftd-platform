import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryFunctionGraph

/-!
# binary_function_graph_adj_const

Topic: graphs   Node: 26f76467b5b3

Provenance: helper lemma. arXiv:2610.37920 Section 2

In the binary function graph of any simple graph on a nonempty vertex set, the constant false and constant true functions are adjacent.
-/

/-- The constant false and constant true functions are adjacent in the binary function graph. -/
lemma binary_function_graph_adj_const {V : Type*} [Nonempty V] (G : SimpleGraph V) : (binary_function_graph G).Adj (fun _ => false) (fun _ => true) := by
  constructor
  · intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    exact Bool.false_ne_true (congr_fun h v)
  · intro b
    have : {v : V | (fun _ => false) v = b ∧ (fun _ => true) v = b} = ∅ := by
      ext v; simp
    rw [this]
    exact Set.pairwise_empty _
