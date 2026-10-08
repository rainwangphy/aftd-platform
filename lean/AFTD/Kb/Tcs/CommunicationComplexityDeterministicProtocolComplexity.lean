import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.complexity

Topic: communication   Node: 183eaf8fa186

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The communication complexity of a protocol $p$ is the worst-case total number of bits
exchanged: an output node costs $0$, while an alice or bob node costs $1$ plus the
maximum complexity of the two sub-protocols reached by the bit $\mathtt{false}$ and the
bit $\mathtt{true}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The communication complexity of a protocol, i.e. the worst-case number of bits exchanged, which is the depth of the protocol tree. [RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. -/
def CommunicationComplexity.Deterministic.Protocol.complexity : Protocol X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity
