import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHypotraceable
import AFTD.Kb.Tcs.Op1952IsTraceableOfIsHamiltonian
import AFTD.Kb.Tcs.SimpleGraphIsTraceable

/-!
# op_1952_not_isHypotraceable_of_isHamiltonian

Topic: graphs   Node: 1d5db271aecf

Provenance: helper lemma. scout/2611-23018-an-infinite-family-of-bipartite-hypotraceable-graphs.md:90

No finite Hamiltonian simple graph on at least two vertices is hypotraceable.
-/

/-- A finite Hamiltonian graph on at least two vertices is not hypotraceable. -/
theorem op_1952_not_isHypotraceable_of_isHamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hH : G.IsHamiltonian) (hn : 2 ≤ Fintype.card V) :
    ¬ G.IsHypotraceable := by
  intro h
  exact h.1 (op_1952_isTraceable_of_isHamiltonian hH hn)
