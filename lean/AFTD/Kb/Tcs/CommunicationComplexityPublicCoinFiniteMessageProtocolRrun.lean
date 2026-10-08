import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun

Topic: communication   Node: 481684bd003b

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathrm{rrun}(p, x, y, \omega)$ executes the protocol $p$ on private inputs $x$ and $y$
with shared randomness $\omega$, defined as $p.\mathrm{run}(\omega, x)\,(\omega, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- The output of the public-coin finite-message protocol `p` on inputs `x`, `y` when the shared random string is `ω`: the deterministic run of `p` on `(ω, x)` and `(ω, y)`. -/
def CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)
