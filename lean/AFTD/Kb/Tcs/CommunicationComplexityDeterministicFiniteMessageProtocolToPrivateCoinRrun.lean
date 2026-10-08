import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoin
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun

Topic: communication   Node: 52305c9fc5a3

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ignoring private coins recovers the deterministic output. Let $p$ be a deterministic finite-message protocol over input types $X$ and $Y$ with
output type $\alpha$, and fix arbitrary private-coin spaces $\Omega_X$ and $\Omega_Y$.
Form from $p$ the private-coin protocol over $\Omega_X$, $\Omega_Y$ that runs $p$ on the
underlying inputs while discarding both players' coins. Then for all inputs $x \in X$,
$y \in Y$ and all coin draws $\omega_x \in \Omega_X$, $\omega_y \in \Omega_Y$, executing
this private-coin protocol on $x$, $y$ with the coins $\omega_x$, $\omega_y$ returns
exactly the value that the deterministic execution of $p$ on $x$, $y$ produces,
regardless of the coins.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- A deterministic finite-message protocol viewed as a private-coin protocol outputs, on `(x, y)` and any coins `ω_x`, `ω_y`, the same value as the deterministic protocol on `(x, y)`. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    PrivateCoin.FiniteMessage.Protocol.rrun
      (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)) x y ω_x ω_y =
      p.run x y := by
  simp [toPrivateCoin, PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]
