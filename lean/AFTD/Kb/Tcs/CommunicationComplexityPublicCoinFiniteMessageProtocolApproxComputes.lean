import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ApproxComputes

Topic: communication   Node: 85c3eb679318

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ApproxComputes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A protocol $p$ $\varepsilon$-computes a function $f : X \to Y \to \alpha$ if for every
input pair $(x, y)$,
\[
  \Pr_{\omega}\bigl[p.\mathrm{rrun}\,x\,y\,\omega \ne f\,x\,y\bigr] \;\le\; \varepsilon.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- A public-coin finite-message protocol `ε`-computes a function `f` if for every input `(x, y)`, the probability (over the shared randomness) of producing an incorrect answer is at most `ε`; this is worst-case error `ε` [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: messages come from arbitrary finite types rather than being single bits. -/
noncomputable def CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω |
      p.rrun x y ω ≠ f x y} ≤ ε
