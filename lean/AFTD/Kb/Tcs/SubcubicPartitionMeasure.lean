import AFTD.Prelude

/-!
# subcubic_partition_measure

Topic: graphs   Node: d4871a860057

Provenance: helper lemma. step towards subcubic_odd_girth_seven_partition

The sum of squares of the orders of the connected components of G[Lᶜ].
-/

open SimpleGraph in
open scoped Classical in
/-- Quality measure for a candidate independent set: sum over connected components of the complement induced subgraph of the square of the component order. -/
noncomputable def subcubic_partition_measure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : Finset V) : ℕ := ∑ C : (G.induce (Lᶜ : Set V)).ConnectedComponent, (Fintype.card C) ^ 2
