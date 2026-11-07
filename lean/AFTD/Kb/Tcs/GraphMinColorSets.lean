import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissibleListAssignment
import AFTD.Kb.Tcs.GraphColorSets

/-!
# graph_min_color_sets

Topic: graphs   Node: 3c78ba994985

Provenance: formalization of a published result. Source: arXiv:2611.07924, Section 1 and Section 2 (Lemma 2.1)

For a finite vertex type V, a simple graph G on V, and an integer m, graph_min_color_sets G m is the infimum sInf of the cardinalities (graph_color_sets G L).card over all admissible list assignments L : V → Finset ℕ of list size m on G.
-/

/-- The minimum number f'(G, m) of distinct color sets used by proper colorings of G from admissible m-element lists. -/
noncomputable def graph_min_color_sets {V : Type*} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : ℕ :=
  sInf { N : ℕ | ∃ L : V → Finset ℕ, is_admissible_list_assignment G m L ∧
    (graph_color_sets G L).card = N }
