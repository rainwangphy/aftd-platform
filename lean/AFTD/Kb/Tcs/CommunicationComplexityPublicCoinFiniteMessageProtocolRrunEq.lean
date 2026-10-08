import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun_eq

Topic: communication   Node: 29f218f3f0ed

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Randomized execution unfolds to deterministic execution. Let $p$ be a public-coin finite-message protocol over shared-randomness space $\Omega$,
private input sets $X$ and $Y$, and output type $\alpha$, and let $x \in X$, $y \in Y$,
and $\omega \in \Omega$. Then the randomized execution of $p$ on inputs $x$ and $y$ with
shared randomness $\omega$ agrees with the deterministic execution of $p$ on Alice's
effective input $(\omega, x)$ and Bob's effective input $(\omega, y)$: \[
\mathrm{rrun}(p, x, y, \omega) = \mathrm{run}(p, (\omega, x), (\omega, y)). \]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- Running a public-coin finite-message protocol on inputs `x`, `y` with randomness `ω` is the same as running the underlying deterministic finite-message protocol on `(ω, x)` and `(ω, y)`. Definitional unfolding lemma for `rrun`. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl
