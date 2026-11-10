import AFTD.Prelude
import AFTD.Kb.Tcs.ProtocolLeafCount
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes

/-!
# min_leaf_count

Topic: communication   Node: cd2a34f7a55f

Provenance: formalization of a published result. Source: arXiv:2611.11488, Section 1.1 and Section 5.1

Given types $X$, $Y$, and $\alpha$ and a function $f : X \to Y \to \alpha$, the minimum protocol leaf count $\mathrm{min\_leaf\_count}(f)$ is the extended natural number in $\mathrm{ENat}$ defined as the infimum of $\mathrm{protocol\_leaf\_count}(p)$ over all deterministic communication protocols $p : \mathrm{CommunicationComplexity.Deterministic.Protocol}\;X\;Y\;\alpha$ satisfying $p.\mathrm{Computes}\;f$.
-/

/-- The minimum number of leaves in any correct deterministic protocol computing f. -/
noncomputable def min_leaf_count {X Y α : Type*} (f : X → Y → α) : ENat := ⨅ (p : CommunicationComplexity.Deterministic.Protocol X Y α) (_ : p.Computes f), (protocol_leaf_count p : ENat)
