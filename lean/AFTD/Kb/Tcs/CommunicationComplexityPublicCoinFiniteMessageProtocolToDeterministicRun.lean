import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministic
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
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
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolToDeterministicRun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic_run

Topic: communication   Node: c87a45f4993f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixing randomness commutes with execution. Let $p$ be a public-coin finite-message protocol over a shared-randomness space
$\Omega$, private input sets $X$ and $Y$, and output type $\alpha$. Fix a randomness
sample $\omega \in \Omega$ and private inputs $x \in X$ and $y \in Y$, and let
$p_\omega$ denote the deterministic finite-message protocol obtained from $p$ by
substituting $\omega$ for the shared randomness. Then executing $p_\omega$ on $x$ and
$y$ yields the same output as the randomized execution of $p$ on $x$ and $y$ with shared
randomness $\omega$:
\[
p_\omega.\mathrm{run}(x, y) \;=\; \mathrm{rrun}(p, x, y, \omega).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Running the deterministic finite-message protocol obtained by fixing the randomness `ω` on `(x, y)` gives the same output as running the public-coin finite-message protocol on `(x, y)` with randomness `ω`. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]
