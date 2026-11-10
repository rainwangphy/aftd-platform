import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLength
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol

/-!
# CommunicationComplexity.PrivateCoin.zeroErrorCommunicationComplexity

Topic: communication   Node: be810508e562

Provenance: formalization of a published result. Source: arXiv:2611.11488 Section 5.2

For types X, Y, and α, and a function f : X → Y → α, the zero-error private-coin expected communication complexity is defined as the infimum (sInf) in ℝ of the set of all real numbers r such that there exist natural numbers nX and nY and a protocol p : PrivateCoin.Protocol (CoinTape nX) (CoinTape nY) X Y α satisfying p.ApproxComputes f 0 and for all x : X and y : Y, the integral over ω : CoinTape nX × CoinTape nY with respect to volume of p.length (ω.1, x) (ω.2, y) cast to ℝ is at most r.
-/

open MeasureTheory in
/-- Zero-error private-coin expected communication complexity. -/
noncomputable def CommunicationComplexity.PrivateCoin.zeroErrorCommunicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ℝ := sInf { r : ℝ | ∃ (nX nY : ℕ) (p : PrivateCoin.Protocol (CoinTape nX) (CoinTape nY) X Y α),
    p.ApproxComputes f 0 ∧
    ∀ (x : X) (y : Y), (∫ (ω : CoinTape nX × CoinTape nY), (p.length (ω.1, x) (ω.2, y) : ℝ)) ≤ r }
