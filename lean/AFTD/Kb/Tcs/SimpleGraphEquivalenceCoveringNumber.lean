import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover

/-!
# simple_graph_equivalence_covering_number

Topic: combinatorics   Node: d0dbce262bc3

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Sec. 1 (definition of eq(G)).

The equivalence covering number eq(G): the minimum number of equivalence subgraphs of G whose edge sets cover E(G).
-/

/-- The equivalence covering number `eq(G)`: the least `t` such that `G` is covered by `t` equivalence subgraphs (0 if there is none, which cannot happen for a finite graph). -/
noncomputable def simple_graph_equivalence_covering_number {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {t | simple_graph_has_equivalence_cover G t}
