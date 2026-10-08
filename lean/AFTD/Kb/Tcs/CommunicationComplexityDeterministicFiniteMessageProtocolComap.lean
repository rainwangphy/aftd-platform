import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap

Topic: communication   Node: 27333d3db5b6

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given maps $f_X : X' \to X$ and $f_Y : Y' \to Y$, the pullback
$p.\mathrm{comap}\,f_X\,f_Y$ is the finite-message protocol over $X'$, $Y'$ obtained by
precomposing every message function with $f_X$ or $f_Y$ respectively, leaving the protocol
tree structure unchanged.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Pull back a finite-message protocol along functions `fX : X' → X` and `fY : Y' → Y`, composing each message function with the maps. -/
def CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    Protocol X' Y' α :=
  match p with
  | .output a => .output a
  | Protocol.alice f P =>
      Protocol.alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | Protocol.bob f P =>
      Protocol.bob (f ∘ fY) (fun b => (P b).comap fX fY)
