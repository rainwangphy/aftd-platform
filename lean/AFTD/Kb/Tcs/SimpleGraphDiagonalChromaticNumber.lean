import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDiagonalConflictGraph

/-!
# simple_graph_diagonal_chromatic_number

Topic: combinatorics   Node: 902deec63aa5

Provenance: formalization of a published result. Source: arXiv:2611.18384 Section 1.1 and line 300

Given a simple graph G on Fin n and a permutation σ on the darts of G, simple_graph_diagonal_chromatic_number G σ is the infimum in ℕ of the set of natural numbers k such that simple_graph_diagonal_conflict_graph G σ is k-colorable.
-/

/-- The diagonal chromatic number χ_d(T) is the chromatic number of the diagonal conflict graph D(T). -/
noncomputable def simple_graph_diagonal_chromatic_number {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm G.Dart) : ℕ :=
  sInf {k : ℕ | (simple_graph_diagonal_conflict_graph G σ).Colorable k}
