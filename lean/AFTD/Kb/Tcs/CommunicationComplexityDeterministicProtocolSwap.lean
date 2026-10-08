import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.swap

Topic: communication   Node: 753a36a76115

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.swap`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a protocol $p$ over $X \times Y$, \texttt{swap} produces a protocol over $Y \times X$
by exchanging the roles of Alice and Bob throughout: every alice node becomes a bob node
and vice versa, while output nodes are left unchanged.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Swaps the roles of Alice and Bob, producing a protocol on `Y × X` from one on `X × Y`. Alice nodes become bob nodes and vice versa. -/
def CommunicationComplexity.Deterministic.Protocol.swap : Protocol X Y α → Protocol Y X α
  | .output val => .output val
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)
