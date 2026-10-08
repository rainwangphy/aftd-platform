import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun

/-!
# CommunicationComplexity.Deterministic.Protocol.Computes

Topic: communication   Node: abc32333d7e5

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.Computes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A protocol $p$ \emph{computes} a two-argument function $f : X \to Y \to \alpha$ if
$p.\texttt{run}\,x\,y = f\,x\,y$ for all inputs $x : X$ and $y : Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A protocol computes a function `f` if it produces `f x y` on all inputs `(x, y)`. [RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. Deviation: the output type `α` is arbitrary rather than Boolean, and the leaf must output `f x y` itself rather than merely determine it. -/
def CommunicationComplexity.Deterministic.Protocol.Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f
