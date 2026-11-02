import AFTD.Prelude
import AFTD.Kb.Tcs.IsCollinearTriple

/-!
# graphNumCollinearTriples

Topic: graphs   Node: 3ecee67ededc

Provenance: formalization of a published result. Source: arXiv:2610.39966 Section 2

The number of collinear triples of a finite simple graph G is the number of 3-element subsets of vertices that are collinear according to IsCollinearTriple.
-/

open scoped Classical in
/-- Number of collinear triples of distinct vertices in a finite simple graph. -/
noncomputable def graphNumCollinearTriples {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (((Finset.univ : Finset V).powersetCard 3).filter (fun T => IsCollinearTriple G (T : Set V))).card
