import AFTD.Prelude

/-!
# CommunicationComplexity.Rectangle.IsRectangle

Topic: communication   Node: c8f84a7908dc

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Rectangle.IsRectangle`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A subset $S \subseteq X \times Y$ is a \emph{rectangle} if it factors as a
product $A \times B$ for some $A \subseteq X$ and $B \subseteq Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A subset of `X × Y` is a (combinatorial) rectangle if it is a product `A ×ˢ B` of a set of `X`-inputs and a set of `Y`-inputs. [RY20, Ch. 1, 'Rectangles'] / [Rou16, §4.2.4 Definition (rectangle)]. -/
def CommunicationComplexity.Rectangle.IsRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B
