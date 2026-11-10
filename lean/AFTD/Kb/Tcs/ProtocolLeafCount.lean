import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# protocol_leaf_count

Topic: communication   Node: 0a875b0b5f4d

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1 and Lemma 3.2

The number of leaves of a deterministic communication protocol $p$ is $1$ if $p$ is an output node, and the sum of the leaf counts of both subtrees if $p$ branches on an Alice or Bob query.
-/

/-- The number of leaves in a deterministic communication protocol tree. -/
def protocol_leaf_count {X Y α : Type*} (p : CommunicationComplexity.Deterministic.Protocol X Y α) : ℕ := match p with
  | CommunicationComplexity.Deterministic.Protocol.output _ => 1
  | CommunicationComplexity.Deterministic.Protocol.alice _ P => protocol_leaf_count (P false) + protocol_leaf_count (P true)
  | CommunicationComplexity.Deterministic.Protocol.bob _ P => protocol_leaf_count (P false) + protocol_leaf_count (P true)
