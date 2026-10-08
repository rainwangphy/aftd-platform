import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxAliceBit
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_disjoint_alice_of_ne

Topic: communication   Node: 6da484866c56

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_disjoint_alice_of_ne`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles on opposite Alice branches are disjoint. Let $p, q$ be protocols on $X \times Y$, let $A \subseteq X$, $B \subseteq Y$, let
$f : X \to \{0,1\}$, and let $b \neq b'$ be distinct bits. If $R$ is a leaf rectangle of
$p$ on $(A \cap \{x \mid f(x) = b\}) \times B$ and $S$ is a leaf rectangle of $q$ on
$(A \cap \{x \mid f(x) = b'\}) \times B$, then $R$ and $S$ are disjoint.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Opposite sides of an `alice` split are disjoint: a leaf rectangle of the child reached on bit `b` and one of the child reached on bit `b' ≠ b` share no input, since no `x` has both `f x = b` and `f x = b'`. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_disjoint_alice_of_ne {p q : Protocol X Y α} {A : Set X} {B : Set Y}
    {f : X → Bool} {b b' : Bool} (hb : b ≠ b') {R S : Set (X × Y)}
    (hR : R ∈ leafRectanglesAux p (A ∩ {x | f x = b}) B)
    (hS : S ∈ leafRectanglesAux q (A ∩ {x | f x = b'}) B) : Disjoint R S := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hxyR hxyS
  exact hb ((aux_alice_bit hR hxyR).symm.trans (aux_alice_bit hS hxyS))
