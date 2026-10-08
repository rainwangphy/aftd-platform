import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap

/-!
# CommunicationComplexity.PrivateCoin.Protocol.rrun_eq

Topic: communication   Node: 85a0425ac621

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PrivateCoin.Protocol.rrun_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Randomized execution as deterministic run on paired inputs. Let $p$ be a private-coin protocol with randomness spaces $\Omega_X$ and $\Omega_Y$,
input spaces $X$ and $Y$, and output type $\alpha$. Then for all inputs $x \in X$ and $y
\in Y$ and all coin outcomes $\omega_x \in \Omega_X$ and $\omega_y \in \Omega_Y$, the
randomized execution of $p$ equals the deterministic execution of $p$ on the paired
inputs $(\omega_x, x)$ and $(\omega_y, y)$:
\[
\mathrm{rrun}(p, x, y, \omega_x, \omega_y) \;=\; \mathrm{run}\bigl(p, (\omega_x, x),
(\omega_y, y)\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- Running a private-coin protocol on inputs `x`, `y` with randomness `ω_x`, `ω_y` is the same as running the underlying deterministic protocol on `(ω_x, x)` and `(ω_y, y)`. Definitional unfolding lemma for `rrun`. -/
@[simp]
theorem CommunicationComplexity.PrivateCoin.Protocol.rrun_eq (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.rrun x y ω_x ω_y = p.run (ω_x, x) (ω_y, y) := rfl
