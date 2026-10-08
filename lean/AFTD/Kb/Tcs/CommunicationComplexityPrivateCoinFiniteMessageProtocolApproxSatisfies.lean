import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxSatisfies

Topic: communication   Node: dc76f1b7382f

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxSatisfies`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A protocol $p$ \emph{$\varepsilon$-satisfies} a predicate $Q : X \to Y \to \alpha \to
\mathrm{Prop}$ if for every input pair $(x, y)$,
\[
  \mathrm{vol}\bigl(\{(\omega_x, \omega_y) \mid \neg Q\,x\,y\,(p.\texttt{rrun}\,x\,y\,\omega_x\,\omega_y)\}\bigr) \;\le\; \varepsilon.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- A finite-message protocol `ε`-satisfies a predicate `Q` if for every input `(x, y)`, the probability that `Q x y (p.rrun ...)` fails is at most `ε`. -/
def CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      ¬Q x y (p.rrun x y ω.1 ω.2)} ≤ ε
