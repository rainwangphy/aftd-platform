import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes

Topic: communication   Node: ec923c3a4996

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A protocol $p$ \emph{$\varepsilon$-computes} a function $f : X \to Y \to \alpha$ if
for every input pair $(x, y)$,
\[
  \mathrm{vol}\bigl(\{(\omega_x, \omega_y) \mid p.\texttt{rrun}\,x\,y\,\omega_x\,\omega_y \ne f\,x\,y\}\bigr) \;\le\; \varepsilon.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- A private-coin finite-message protocol `ε`-computes a function `f` if for every input `(x, y)`, the probability (over the product of the two private randomness spaces) of producing an incorrect answer is at most `ε`; this is worst-case error `ε` [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: messages come from arbitrary finite types rather than being single bits. -/
noncomputable def CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y} ≤ ε
