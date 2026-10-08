import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun

/-!
# CommunicationComplexity.PrivateCoin.Protocol.ApproxComputes

Topic: communication   Node: 432fd9b45b14

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.Protocol.ApproxComputes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A private-coin protocol $p$ \emph{$\varepsilon$-computes} a function $f : X \to Y \to \alpha$ if
for every input pair $(x, y)$,
\[
  \mu\!\left\{\,\omega \in \Omega_X \times \Omega_Y \;\middle|\;
    p.\mathrm{rrun}\;x\;y\;\omega_1\;\omega_2 \ne f\,x\,y\,\right\} \;\le\; \varepsilon.
\]
This formalises the standard notion of bounded-error private-coin randomized
communication complexity.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- A private-coin protocol `ε`-computes a function `f` if for every input `(x, y)`, the probability (under the product of the two coin-flip measures) of producing an incorrect answer is at most `ε`; this is worst-case error `ε` [RY20, Ch. 3, §Variants of Randomized Protocols: worst-case error e]. -/
noncomputable def CommunicationComplexity.PrivateCoin.Protocol.ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε
