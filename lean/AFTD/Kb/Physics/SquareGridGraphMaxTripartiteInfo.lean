import AFTD.Prelude
import AFTD.Kb.Physics.SquareGridGraphTripartiteInfo

/-!
# square_grid_graph_max_tripartite_info

Topic: quantum_mechanics   Node: 352e7b11fdc3

Provenance: formalization of a published result. Source: arXiv:2511.19585 ("Monogamy of Mutual Information in Graph States")

For any natural number n, square_grid_graph_max_tripartite_info n is the maximum tripartite information M_n over all four-colorings c on the n-by-n square grid graph state.
-/

/-- Maximum tripartite information M_n of the n-by-n square grid graph state over all four-partitions. -/
noncomputable def square_grid_graph_max_tripartite_info (n : ℕ) : ℤ := ((Finset.univ : Finset (Fin n × Fin n → Fin 4)).image (square_grid_graph_tripartite_info n)).max' (by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty)
