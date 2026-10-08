import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.run

Topic: communication   Node: 3d61a4371409

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a finite-message protocol $p$ and inputs $x : X$, $y : Y$, \texttt{run} executes $p$
recursively: at an \texttt{alice} node it evaluates $f(x)$ and follows the corresponding
continuation, at a \texttt{bob} node it evaluates $f(y)$, and at an \texttt{output} node it
returns the stored value.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Executes the generalized protocol on inputs `x` and `y`, returning the output value: the owner of the current node evaluates its message function on its own input and both parties descend to the child indexed by that message, until a leaf is reached. -/
def CommunicationComplexity.Deterministic.FiniteMessage.Protocol.run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | Deterministic.FiniteMessage.Protocol.output val => val
  | Deterministic.FiniteMessage.Protocol.alice f P => (P (f x)).run x y
  | Deterministic.FiniteMessage.Protocol.bob f P => (P (f y)).run x y
