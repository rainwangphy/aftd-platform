import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice

Topic: communication   Node: 8034be6df48b

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An auxiliary construction: given $d$ binary query functions $\mathrm{query}_i : X \to
\mathrm{Bool}$ and a family of binary protocols $Q : (\mathrm{Fin}\,d \to \mathrm{Bool}) \to
\mathrm{Protocol}\,X\,Y\,\alpha$, builds a single binary protocol that reads each query bit
from Alice in sequence and then runs $Q$ on the collected bit pattern.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The complete binary protocol tree of depth `d` in which Alice sends the `d` bits `query 0 x, …, query (d-1) x` in order and the protocol then continues as `Q bits`, where `bits` is the vector of bits sent. -/
def CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) : Deterministic.Protocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => Deterministic.Protocol.alice (query 0) (fun b =>
      completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons b bits)))
