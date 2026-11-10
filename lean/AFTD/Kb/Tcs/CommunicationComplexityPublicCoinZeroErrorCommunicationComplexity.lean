import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLength
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape

/-!
# CommunicationComplexity.PublicCoin.zeroErrorCommunicationComplexity

Topic: communication   Node: 142a26281a37

Provenance: formalization of a published result. Source: arXiv:2611.11488 Section 5.2, equation (5.1)

For types X, Y, and α, and a function f : X → Y → α, the zero-error public-coin expected communication complexity is defined as the infimum (sInf) in ℝ of the set of all real numbers r such that there exists a natural number n and a protocol p : PublicCoin.Protocol (CoinTape n) X Y α satisfying p.ApproxComputes f 0 and for all x : X and y : Y, the integral over ω : CoinTape n with respect to volume of p.length (ω, x) (ω, y) cast to ℝ is at most r.
-/

open MeasureTheory in
/-- Zero-error public-coin expected communication complexity. -/
noncomputable def CommunicationComplexity.PublicCoin.zeroErrorCommunicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ℝ := sInf { r : ℝ | ∃ (n : ℕ) (p : PublicCoin.Protocol (CoinTape n) X Y α),
    p.ApproxComputes f 0 ∧
    ∀ (x : X) (y : Y), (∫ (ω : CoinTape n), (p.length (ω, x) (ω, y) : ℝ)) ≤ r }
