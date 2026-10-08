import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol

/-!
# CommunicationComplexity.PrivateCoin.Protocol.rrun

Topic: communication   Node: a861d9744f20

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.Protocol.rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{rrun}\;p\;x\;y\;\omega_x\;\omega_y$ executes the private-coin protocol $p$ on
inputs $x \in X$ and $y \in Y$ with Alice's private coin $\omega_x \in \Omega_X$ and
Bob's private coin $\omega_y \in \Omega_Y$, returning the output $\alpha$.  It is
defined by $p.\mathrm{run}\,(\omega_x, x)\,(\omega_y, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- The output of the private-coin protocol `p` on inputs `x`, `y` when Alice's private random string is `ω_x` and Bob's is `ω_y`: the deterministic run of `p` on `(ω_x, x)` and `(ω_y, y)` [RY20, Ch. 3, §Variants of Randomized Protocols: private coins]. -/
def CommunicationComplexity.PrivateCoin.Protocol.rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)
