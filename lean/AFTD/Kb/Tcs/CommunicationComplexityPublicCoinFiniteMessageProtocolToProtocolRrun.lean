import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_rrun

Topic: communication   Node: 95647d4100b9

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Binary conversion preserves randomized execution. Let $p$ be a public-coin finite-message protocol with shared-randomness space $\Omega$,
private input sets $X$ and $Y$, and output type $\alpha$, and let $q$ be the binary
public-coin protocol obtained from $p$ by encoding each finite-alphabet message as a
string of bits. Then for every pair of private inputs $x \in X$ and $y \in Y$ and every
shared random string $\omega \in \Omega$, the two protocols produce the same output when
executed on those inputs with that randomness: the randomized execution of $q$ on $x$,
$y$, $\omega$ equals the randomized execution of $p$ on $x$, $y$, $\omega$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- The binary public-coin protocol obtained from a finite-message protocol `p` by `toProtocol` has the same output as `p` on every input `x`, `y` and every random string `ω`. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_rrun (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.toProtocol).rrun x y ω = p.rrun x y ω := by
  simp [PublicCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]
