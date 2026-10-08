import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxSubset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_bob_bit

Topic: communication   Node: efcf4e488698

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_bob_bit`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bob's bit is fixed on a child's leaf rectangle. Let $p$ be a protocol on $X \times Y$, let $A \subseteq X$, $B \subseteq Y$, let
$f : Y \to \{0,1\}$ be the bit Bob sends, and let $b$ be a bit. If $R$ is a leaf
rectangle of $p$ run on the restricted input set $A \times (B \cap \{y \mid f(y) = b\})$,
then every input $(x, y) \in R$ satisfies $f(y) = b$. This is the mirror image of
$ CommunicationComplexity.Deterministic.Protocol.aux_alice_bit$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Shared bit-split step of the `bob` branches: a leaf rectangle of the child reached on Bob's bit `b` only contains inputs `(x, y)` with `f y = b`; mirror of `aux_alice_bit`. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_bob_bit {p : Protocol X Y α} {A : Set X} {B : Set Y} {f : Y → Bool}
    {b : Bool} {R : Set (X × Y)} (hR : R ∈ leafRectanglesAux p A (B ∩ {y | f y = b}))
    {x : X} {y : Y} (hxy : (x, y) ∈ R) : f y = b :=
  (aux_subset p _ _ R hR hxy).2.2
