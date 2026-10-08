import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectanglesAux

Topic: communication   Node: 023dddf5baed

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectanglesAux`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a protocol $p$ and sets $A \subseteq X$, $B \subseteq Y$, $\texttt{leafRectanglesAux}(p, A, B)$
is the collection of rectangles induced by the leaves of $p$ when the reachable inputs are
constrained to $A \times B$. It is defined by structural recursion: an output node yields
$\{A \times B\}$, while Alice (resp.\ Bob) nodes split $A$ (resp.\ $B$) according to the
branching function and recurse.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The leaf rectangles of a protocol relative to a constraint rectangle `A ×ˢ B`, i.e. the sets of inputs in `A ×ˢ B` reaching each leaf: a terminal protocol contributes `A ×ˢ B` itself, an Alice node with message function `f` the leaf rectangles of the child reached on bit `b` relative to `(A ∩ {x | f x = b}) ×ˢ B` for both `b`, and a Bob node likewise with the constraint on `B`. `leafRectangles` is the case `A = B = univ`. -/
def CommunicationComplexity.Deterministic.Protocol.leafRectanglesAux (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})
