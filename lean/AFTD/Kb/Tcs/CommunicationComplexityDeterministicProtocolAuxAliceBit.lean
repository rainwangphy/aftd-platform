import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxSubset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_alice_bit

Topic: communication   Node: 35a54961018e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_alice_bit`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Alice's bit is fixed on a child's leaf rectangle. Let $p$ be a protocol on $X \times Y$, let $A \subseteq X$, $B \subseteq Y$, let
$f : X \to \{0,1\}$ be the bit Alice sends, and let $b$ be a bit. If $R$ is a leaf
rectangle of $p$ run on the restricted input set $(A \cap \{x \mid f(x) = b\}) \times B$,
then every input $(x, y) \in R$ satisfies $f(x) = b$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Shared bit-split step of the `alice` branches: a leaf rectangle of the child reached on Alice's bit `b` only contains inputs `(x, y)` with `f x = b` (via `aux_subset`). -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_alice_bit {p : Protocol X Y α} {A : Set X} {B : Set Y} {f : X → Bool}
    {b : Bool} {R : Set (X × Y)} (hR : R ∈ leafRectanglesAux p (A ∩ {x | f x = b}) B)
    {x : X} {y : Y} (hxy : (x, y) ∈ R) : f x = b :=
  (aux_subset p _ _ R hR hxy).1.2
