import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInternalSingleCoinApprox
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

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape

Topic: communication   Node: f68c2df3a737

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a public-coin finite-message protocol $p$ over an arbitrary finite probability
space $\Omega$ and a slack $\delta > 0$, this definition produces a natural number $n$
together with a finite-message protocol over $\mathrm{CoinTape}(n)$ that approximates
$p$. The construction works by pulling back $p$ along a measure-approximating map
$\varphi : \mathrm{CoinTape}(n) \to \Omega$ provided by
\texttt{CommunicationComplexity.Internal.single\_coin\_approx}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The coin-tape approximation of a public-coin finite-message protocol `p` over an arbitrary finite probability space `Ω` with slack `δ > 0`: a length `n` together with a protocol over `CoinTape n` obtained by pulling `p` back along a map `φ : CoinTape n → Ω` (chosen by `Internal.single_coin_approx`) under which every event of `Ω` is approximated to within `δ`. The result has the same complexity as `p` and, on every input, an error probability at most `δ` larger. -/
noncomputable def CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toCoinTape
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (n : ℕ), FiniteMessage.Protocol (CoinTape n) X Y α :=
  let data := Internal.single_coin_approx (Ω := Ω) δ hδ
  let n := data.choose
  let φ := data.choose_spec.choose
  ⟨n, p.comap (Prod.map φ id) (Prod.map φ id)⟩
