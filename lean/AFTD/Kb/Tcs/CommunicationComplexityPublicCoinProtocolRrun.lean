import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol

/-!
# CommunicationComplexity.PublicCoin.Protocol.rrun

Topic: communication   Node: be2265c12537

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.Protocol.rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a public-coin protocol $p$, private inputs $x \in X$, $y \in Y$, and a shared
random string $\omega \in \Omega$, $\texttt{rrun}\,p\,x\,y\,\omega$ executes the
underlying deterministic protocol on the paired inputs $(\omega, x)$ and $(\omega, y)$
and returns the resulting output.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- The output of the public-coin protocol `p` on inputs `x`, `y` when the shared random string is `ω`: the deterministic run of `p` on `(ω, x)` and `(ω, y)` [RY20, Ch. 3, §Variants of Randomized Protocols: public coins]. -/
def CommunicationComplexity.PublicCoin.Protocol.rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)
