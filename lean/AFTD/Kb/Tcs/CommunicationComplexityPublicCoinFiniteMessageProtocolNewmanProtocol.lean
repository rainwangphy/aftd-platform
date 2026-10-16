import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoin
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministic
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolExistsGoodRandomness
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolAlice
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityUnitMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityUnitFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceNonempty
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol

Topic: communication   Node: 1b5d3b555f84

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a public-coin finite-message protocol $p$ over a probability space $\Omega$ that
$\varepsilon$-computes $f : X \to Y \to \alpha$, and a constant $c > 1$, the Newman protocol
is a private-coin finite-message protocol in which Alice draws a random index $i$ from
$\mathtt{newmanIndexSpace}\;X\;Y\;\varepsilon\;c$ and sends it to Bob; both players then
run the $i$-th seed from a fixed table of good randomness values (obtained via a Chernoff
and union-bound argument) through the original public-coin protocol deterministically.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The Newman private-coin protocol built from a public-coin protocol `p` that ε-computes `f`: Alice samples a random index `i` from `newmanIndexSpace` (her private randomness; Bob has none) and sends it to Bob, and both then run the deterministic protocol obtained from `p` by fixing its public randomness to the `i`-th seed of a fixed table of good seeds (the table is the witness of `exists_good_randomness`, obtained by a Chernoff + union bound). [RY20, Thm 3.5 proof] (Alice sends the index of one of the `t` good strings). -/
noncomputable def CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    PrivateCoin.FiniteMessage.Protocol
      (newmanIndexSpace X Y ε c) Unit X Y α :=
  -- Choose good randomness values via Chernoff + union bound
  let ωs := (FiniteMessage.Protocol.exists_good_randomness
    p f ε c hc hp).choose
  -- Alice sends her random index i ∈ newmanIndexSpace to Bob,
  -- then both simulate with ωs(i)
  PrivateCoin.FiniteMessage.Protocol.alice
    (fun _ ω_x => ω_x)
    (fun i => (p.toDeterministic (ωs i)).toPrivateCoin)
