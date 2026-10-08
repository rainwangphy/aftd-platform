import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol

Topic: communication   Node: 2152eb449925

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A generalized deterministic two-party communication protocol over input types $X$, $Y$ and
output type $\alpha$.  At each step a player sends an element of an arbitrary finite nonempty
type $\beta$: the \texttt{alice} constructor takes a function $f : X \to \beta$ and a
continuation $P : \beta \to \mathrm{Protocol}\,X\,Y\,\alpha$, and dually for \texttt{bob}.
The \texttt{output} constructor terminates the protocol with a value in $\alpha$.  This
inductive type is equivalent to the binary \texttt{Deterministic.Protocol} up to complexity,
where a $\beta$-valued message costs $\lceil \log_2 |\beta| \rceil$ bits.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A generalized deterministic two-party communication protocol where at each step, a player sends an element of an arbitrary finite type `β` (rather than just a `Bool`). [RY20, Ch. 1, Definition (2-party deterministic protocol)]. Deviation: messages come from an arbitrary nonempty finite alphabet `β` (which may vary from node to node) instead of bits. Equivalent to `Deterministic.Protocol` up to complexity (see `toProtocol`) where sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive CommunicationComplexity.Deterministic.FiniteMessage.Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → β) (P : β → Protocol X Y α) :
      Protocol X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → β) (P : β → Protocol X Y α) :
      Protocol X Y α
