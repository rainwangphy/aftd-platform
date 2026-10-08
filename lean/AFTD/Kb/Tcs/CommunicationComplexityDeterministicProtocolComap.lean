import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.comap

Topic: communication   Node: eca04b8432fc

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.comap`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given functions $f_X : X' \to X$ and $f_Y : Y' \to Y$, \texttt{comap} pulls back a protocol
$p$ over $X \times Y$ to a protocol over $X' \times Y'$ by pre-composing every message
function with $f_X$ or $f_Y$ as appropriate, leaving output nodes unchanged.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Pull back a protocol along functions `fX : X' → X` and `fY : Y' → Y`. The resulting protocol over `X' × Y'` simulates the original by applying `fX` and `fY` to the inputs before each message function. -/
def CommunicationComplexity.Deterministic.Protocol.comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) : Protocol X' Y' α :=
  match p with
  | .output val => .output val
  | .alice f P => .alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | .bob f P => .bob (f ∘ fY) (fun b => (P b).comap fX fY)
