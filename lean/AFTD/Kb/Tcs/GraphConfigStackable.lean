import AFTD.Prelude
import AFTD.Kb.Tcs.GraphPebblingStep

/-!
# graph_config_stackable

Topic: graphs   Node: 2d1a97b501c1

Provenance: formalization of a published result. Source: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 2.1 (stacked, stackable).

A configuration c on G is stackable if a sequence of pebbling steps (possibly empty) turns it into a stacked configuration, one whose support is a single vertex.
-/

/-- `c` is stackable on `G`: some configuration reachable from `c` by pebbling steps has support exactly one vertex. -/
def graph_config_stackable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  ∃ c', Relation.ReflTransGen (graph_pebbling_step G) c c' ∧
    ∃ v, 0 < c' v ∧ ∀ w, w ≠ v → c' w = 0
