import AFTD.Prelude

/-!
# is_conference_graph

Topic: combinatorics   Node: 0ca9b236d505

Provenance: formalization of a published result. Source: arXiv:2610.36522 Definition 6

A conference graph is a strongly regular graph srg(v, (v-1)/2, (v-5)/4, (v-1)/4) with v ≡ 1 mod 4.
-/

/-- Predicate for a graph being a conference graph of order v ≡ 1 mod 4. -/
def is_conference_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsSRGWith (Fintype.card V) ((Fintype.card V - 1) / 2) ((Fintype.card V - 5) / 4) ((Fintype.card V - 1) / 4) ∧
    Fintype.card V % 4 = 1
