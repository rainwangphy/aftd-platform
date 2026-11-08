import AFTD.Prelude
import AFTD.Kb.Tcs.StabilizedSubspace
import AFTD.Kb.Tcs.ClosedNetworkEndNodeResponseBound

/-!
# stabilizedSubspace_bot

Topic: quantum   Node: a687adae9549

Provenance: helper lemma. arXiv:2610.37807 Definition 4

For any natural number $n$, the stabilized subspace of the trivial subgroup $\bot \le (\mathrm{Matrix}\,(\mathrm{Fin}\,(2^n))\,(\mathrm{Fin}\,(2^n))\,\mathbb{C})^\times$ is the full module $\top$.
-/

/-- The stabilized subspace of the trivial subgroup is the entire space. -/
theorem stabilizedSubspace_bot (n : ℕ) : stabilizedSubspace n ⊥ = ⊤ := by first | exact closed_network_end_node_response_bound | (apply closed_network_end_node_response_bound <;> assumption) | (apply closed_network_end_node_response_bound <;> simp_all) | simpa using closed_network_end_node_response_bound | (simp only [stabilizedSubspace] at *; first | exact closed_network_end_node_response_bound | (apply closed_network_end_node_response_bound <;> assumption) | (apply closed_network_end_node_response_bound <;> simp_all) | simpa using closed_network_end_node_response_bound)
