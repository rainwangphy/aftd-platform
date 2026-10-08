import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.PublicCoin.Protocol.rrun_eq

Topic: communication   Node: 57a786ebfae5

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.Protocol.rrun_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Randomized execution as deterministic execution on paired inputs. Let $p$ be a public-coin protocol with shared randomness in $\Omega$, Alice's private
input in $X$, and Bob's in $Y$, producing an output in $\alpha$. Then for every $x \in
X$, $y \in Y$, and $\omega \in \Omega$, the randomized execution of $p$ on $x$, $y$ with
random string $\omega$ equals the execution of the underlying deterministic protocol on
the paired inputs $(\omega, x)$ and $(\omega, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- Running a public-coin protocol on inputs `x`, `y` with randomness `ω` is the same as running the underlying deterministic protocol on `(ω, x)` and `(ω, y)`. Definitional unfolding lemma for `rrun`. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.Protocol.rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl
