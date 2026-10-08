import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxBobBit
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_disjoint_bob_of_ne

Topic: communication   Node: f0f06d29cb72

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_disjoint_bob_of_ne`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles on opposite Bob branches are disjoint. Let $p, q$ be protocols on $X \times Y$, let $A \subseteq X$, $B \subseteq Y$, let
$f : Y \to \{0,1\}$, and let $b \neq b'$ be distinct bits. If $R$ is a leaf rectangle of
$p$ on $A \times (B \cap \{y \mid f(y) = b\})$ and $S$ is a leaf rectangle of $q$ on
$A \times (B \cap \{y \mid f(y) = b'\})$, then $R$ and $S$ are disjoint. This is the
mirror image of $ CommunicationComplexity.Deterministic.Protocol.aux_disjoint_alice_of_ne$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Opposite sides of a `bob` split are disjoint; mirror of `aux_disjoint_alice_of_ne`. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_disjoint_bob_of_ne {p q : Protocol X Y α} {A : Set X} {B : Set Y}
    {f : Y → Bool} {b b' : Bool} (hb : b ≠ b') {R S : Set (X × Y)}
    (hR : R ∈ leafRectanglesAux p A (B ∩ {y | f y = b}))
    (hS : S ∈ leafRectanglesAux q A (B ∩ {y | f y = b'})) : Disjoint R S := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hxyR hxyS
  exact hb ((aux_bob_bit hR hxyR).symm.trans (aux_bob_bit hS hxyS))
