import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.Protocol.ApproxComputes

Topic: communication   Node: 82f4ec1fb6de

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.Protocol.ApproxComputes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A public-coin protocol $p$ \emph{$\varepsilon$-computes} a function
$f : X \to Y \to \alpha$ if for every input pair $(x, y)$,
\[
  \mathrm{vol}\bigl\{\omega \in \Omega \mid p.\texttt{rrun}\,x\,y\,\omega \ne f\,x\,y\bigr\} \;\le\; \varepsilon.
\]
Here the volume is taken with respect to the measure on $\Omega$ given by the
\texttt{MeasureSpace} instance.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- A public-coin protocol `ε`-computes a function `f` if for every input `(x, y)`, the probability (under the shared coin-flip measure) of producing an incorrect answer is at most `ε`; this is worst-case error `ε` [RY20, Ch. 3, §Variants of Randomized Protocols: worst-case error e]. -/
noncomputable def CommunicationComplexity.PublicCoin.Protocol.ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      p.rrun x y ω ≠ f x y}).toReal ≤ ε
