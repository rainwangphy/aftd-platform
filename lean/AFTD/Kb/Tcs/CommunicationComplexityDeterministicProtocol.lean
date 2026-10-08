import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.Protocol

Topic: communication   Node: a256518caf97

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A deterministic two-party communication protocol over input types $X$ (Alice) and $Y$ (Bob)
producing a value of type $\alpha$ is an inductive type with three constructors: an
\emph{output} node carrying the final value, an \emph{alice} node in which Alice applies a
function $f : X \to \mathrm{Bool}$ to her input and branches on the resulting bit, and a
\emph{bob} node in which Bob does the same with a function $g : Y \to \mathrm{Bool}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A deterministic two-party communication protocol where Alice holds input `x : X`, Bob holds input `y : Y`, and the protocol computes a value of type `α`. At each step, either Alice or Bob sends a single bit based on their input, and the protocol branches accordingly. [RY20, Ch. 1, Definition (2-party deterministic protocol)]. The tree is represented inductively: a leaf carries the output value, and an internal node carries its owner's message function together with the two subtrees. -/
inductive CommunicationComplexity.Deterministic.Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice (f : X → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
  | bob (f : Y → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
