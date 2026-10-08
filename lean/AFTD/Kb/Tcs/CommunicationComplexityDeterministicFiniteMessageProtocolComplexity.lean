import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.complexity

Topic: communication   Node: 84b230622bc2

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The worst-case communication cost of a finite-message protocol, measured in bits.  An
\texttt{output} node costs $0$; an \texttt{alice} or \texttt{bob} node with message type
$\beta$ costs $\lceil \log_2 |\beta| \rceil$ plus the maximum complexity over all continuations,
i.e.\ $\lceil \log_2 |\beta| \rceil + \sup_{b \in \beta} \mathrm{complexity}(P\,b)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The communication complexity of a generalized protocol. Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits, reflecting the number of bits needed to encode an element of `β`. -/
def CommunicationComplexity.Deterministic.FiniteMessage.Protocol.complexity : Protocol X Y α → ℕ
  | Deterministic.FiniteMessage.Protocol.output _ => 0
  | Deterministic.FiniteMessage.Protocol.alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | Deterministic.FiniteMessage.Protocol.bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
