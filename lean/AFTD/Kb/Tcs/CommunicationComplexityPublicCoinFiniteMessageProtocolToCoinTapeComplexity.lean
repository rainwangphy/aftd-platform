import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity

Topic: communication   Node: 4034d0760664

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coin-tape conversion preserves complexity. Let $\Omega$ be a finite probability space, and let $p$ be a public-coin finite-message
protocol over shared randomness $\Omega$ with input sets $X$, $Y$ and output type
$\alpha$. For every real number $\delta > 0$, the coin-tape conversion of $p$ at slack
$\delta$ yields a length $n$ and a finite-message protocol over $\mathrm{CoinTape}(n)$
whose communication complexity equals the communication complexity of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The coin-tape approximation of a public-coin finite-message protocol `p` has exactly the complexity of `p`: pulling back along the map on randomness changes no message. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]
