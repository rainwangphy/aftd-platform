import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoin
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

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity

Topic: communication   Node: 6728519e9651

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Complexity is preserved by passage to the private-coin model. Let $p$ be a deterministic finite-message protocol over input types $X$, $Y$ and output
type $\alpha$, and let $\Omega_X$, $\Omega_Y$ be arbitrary types to serve as
private-randomness spaces. Form the private-coin finite-message protocol over
$\Omega_X$, $\Omega_Y$ obtained from $p$ by having each player ignore their private
coin, so that Alice's message function $f : X \to \beta$ is replaced by $(\omega, x)
\mapsto f(x)$ and Bob's by $(\omega, y) \mapsto f(y)$, with the protocol tree otherwise
unchanged. Then this private-coin protocol has the same communication complexity as $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Viewing a deterministic finite-message protocol as a private-coin protocol does not change its complexity. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)).complexity =
      p.complexity := by
  simp [toPrivateCoin]
