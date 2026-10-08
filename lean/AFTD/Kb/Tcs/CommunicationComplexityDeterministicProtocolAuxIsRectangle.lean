import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_isRectangle

Topic: communication   Node: 03b5bb076745

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_isRectangle`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auxiliary leaf sets are rectangles. Let $p$ be a deterministic two-party communication protocol over input types $X$ (Alice)
and $Y$ (Bob), and let $A \subseteq X$ and $B \subseteq Y$. Then every set belonging to
the auxiliary leaf-rectangle collection of $p$ relative to the constraint $A \times B$
is a rectangle; that is, if $R \subseteq X \times Y$ is one of these leaf sets, then $R
= A' \times B'$ for some $A' \subseteq X$ and $B' \subseteq Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Every leaf rectangle of `p` relative to `A ×ˢ B` is a combinatorial rectangle. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_isRectangle (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : Rectangle.IsRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
