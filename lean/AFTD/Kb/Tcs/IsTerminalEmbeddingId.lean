import AFTD.Prelude
import AFTD.Kb.Tcs.IsTerminalEmbedding

/-!
# is_terminal_embedding_id

Topic: algorithms   Node: c09869f8cc63

Provenance: helper lemma. arXiv:2611.08546 "Bourgain's Theorem for a Union of Euclidean Metric Spaces", Definition 2.1

For every metric space X and every subset V of X, the identity map id on X is a terminal embedding for V.
-/

/-- The identity map on a metric space X is a terminal embedding for any subset V ⊆ X. -/
lemma is_terminal_embedding_id.{u} {X : Type u} [MetricSpace X] (V : Set X) :
    IsTerminalEmbedding V (id : X → X) := ⟨LipschitzWith.id, fun _ _ _ => rfl⟩
