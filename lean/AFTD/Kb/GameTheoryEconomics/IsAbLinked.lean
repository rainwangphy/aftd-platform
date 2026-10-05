import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet

/-!
# is_ab_linked

Topic: fair_division   Node: ed9f202255a6

A graph G is (a,b)-linked if for any disjoint vertex sets M1, M2 with |M1| = a and |M2| = b there are disjoint vertex sets S1 ⊇ M1 and S2 ⊇ M2, each inducing a connected subgraph.
-/

/-- (a,b)-linkedness: any disjoint `M1`, `M2` of sizes `a`, `b` extend to disjoint connected vertex sets `S1 ⊇ M1`, `S2 ⊇ M2`. -/
def is_ab_linked {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ M1 M2 : Finset V, Disjoint M1 M2 → M1.card = a → M2.card = b →
    ∃ S1 S2 : Set V, Disjoint S1 S2 ∧ (↑M1 : Set V) ⊆ S1 ∧ (↑M2 : Set V) ⊆ S2 ∧
      is_connected_vertex_set G S1 ∧ is_connected_vertex_set G S2
