import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_cover

Topic: communication   Node: c66152dbd50b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_cover`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles cover the input rectangle. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from a set $X$, Bob's inputs from a set $Y$, and outputs in a type $\alpha$, and let $A
\subseteq X$ and $B \subseteq Y$. Then the rectangle $A \times B$ is contained in the
union of the auxiliary leaf rectangles of $p$ relative to the constraint $A \times B$;
that is, every pair $(x, y) \in A \times B$ lies in at least one rectangle of this
collection.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The leaf rectangles of `p` relative to `A ×ˢ B` cover `A ×ˢ B`: an input `(x, y)` lies in the rectangle of the leaf it reaches, found by following its bits down the tree. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_cover (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    A ×ˢ B ⊆ ⋃₀ leafRectanglesAux p A B := by
  induction p generalizing A B with
  | output _ =>
    intro xy hxy
    exact Set.mem_sUnion.mpr ⟨_, Set.mem_singleton _, hxy⟩
  | alice f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f x with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨⟨hx, hf⟩, hy⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨⟨hx, hf⟩, hy⟩)
  | bob f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f y with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨hx, ⟨hy, hf⟩⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨hx, ⟨hy, hf⟩⟩)
