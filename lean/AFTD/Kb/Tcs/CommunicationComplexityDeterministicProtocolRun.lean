import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.run

Topic: communication   Node: bceb63fdf7be

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a protocol $p$, \texttt{run} evaluates $p$ on inputs $x : X$ and $y : Y$ by
recursively following the bit-branching structure until an output node is reached,
returning the stored value of type $\alpha$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Executes the protocol on inputs `x` and `y`, returning the output value: starting at the root, the owner of the current node evaluates its message function on its own input and both parties descend to the indicated child, until a leaf is reached. [RY20, Ch. 1, Definition (outcome)]. -/
def CommunicationComplexity.Deterministic.Protocol.run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | .output val => val
  | .alice f P => (P (f x)).run x y
  | .bob f P => (P (f y)).run x y
