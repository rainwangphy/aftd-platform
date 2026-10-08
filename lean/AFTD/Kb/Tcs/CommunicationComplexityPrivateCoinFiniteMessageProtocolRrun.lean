import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rrun

Topic: communication   Node: fa547b07e6a6

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{rrun}\,p\,x\,y\,\omega_x\,\omega_y$ executes the protocol $p$ on public inputs
$x : X$, $y : Y$ with Alice's private coin $\omega_x : \Omega_X$ and Bob's private coin
$\omega_y : \Omega_Y$, returning an element of $\alpha$.  It is defined by running the
underlying deterministic protocol on the paired inputs $(\omega_x, x)$ and
$(\omega_y, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- The output of the private-coin finite-message protocol `p` on inputs `x`, `y` when Alice's private random string is `ω_x` and Bob's is `ω_y`: the deterministic run of `p` on `(ω_x, x)` and `(ω_y, y)`. -/
def CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)
