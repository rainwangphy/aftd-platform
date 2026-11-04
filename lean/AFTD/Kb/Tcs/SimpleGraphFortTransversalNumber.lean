import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsFort
import AFTD.Kb.Tcs.IsCompatibleCollection
import AFTD.Kb.Tcs.FinsetTransversalNumber

/-!
# simple_graph_fort_transversal_number

Topic: graphs   Node: de310e410f44

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 2, equation (2.3)

The fort transversal number T(G) of a finite simple graph G on a finite type V with decidable equality is the supremum of the transversal numbers of all compatible finite collections C of forts of G.
-/

/-- The fort transversal number T(G) of G is the maximum transversal number of a compatible collection of forts. -/
noncomputable def simple_graph_fort_transversal_number {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := sSup { k : ℕ | ∃ C : Finset (Finset V),
    (∀ F ∈ C, simple_graph_is_fort G (F : Set V)) ∧ is_compatible_collection C ∧ finset_transversal_number C = k }
