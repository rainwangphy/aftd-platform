import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInternalProductCoinApprox
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape

Topic: communication   Node: 79e4dc9aa8dc

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a finite-message private-coin protocol $p$ over finite probability spaces $\Omega_X$
and $\Omega_Y$, and a tolerance $\delta > 0$, $\mathrm{toCoinTape}(p, \delta)$ produces
$n_X$, $n_Y$, and a new finite-message protocol over $\mathrm{CoinTape}(n_X) \times
\mathrm{CoinTape}(n_Y)$ obtained by precomposing $p$ with the inverse-CDF approximating
maps $\varphi_X$ and $\varphi_Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- The coin-tape approximation of a private-coin finite-message protocol `p` over arbitrary finite probability spaces: given `δ > 0`, the tape lengths `nX`, `nY` and the maps `φ_X`, `φ_Y` of `product_coin_approx` are chosen, and the protocol is `p` with Alice's and Bob's coins pulled back along `φ_X` and `φ_Y`. It has the same complexity as `p`, and its error on every input exceeds that of `p` by at most `δ` (`toCoinTape_approxSatisfies`). This is the discretisation step of Newman's theorem [New91]; the construction does not depend on any correctness predicate `Q`. -/
noncomputable def CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (nX : ℕ) (nY : ℕ),
      FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α :=
  let data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  let nX := data.choose
  let nY := data.choose_spec.choose
  let φ_X := data.choose_spec.choose_spec.choose
  let φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  ⟨nX, nY, p.comap (Prod.map φ_X id) (Prod.map φ_Y id)⟩
