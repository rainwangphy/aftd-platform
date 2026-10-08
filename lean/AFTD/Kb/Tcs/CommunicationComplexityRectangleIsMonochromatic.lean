import AFTD.Prelude

/-!
# CommunicationComplexity.Rectangle.IsMonochromatic

Topic: communication   Node: 43ab01919382

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Rectangle.IsMonochromatic`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A set $S \subseteq X \times Y$ is \emph{monochromatic} for a function
$g : X \to Y \to \alpha$ if $g$ is constant on $S$, i.e., $g\,x\,y = g\,x'\,y'$
for all $(x,y), (x',y') \in S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A set `S ⊆ X × Y` is monochromatic for `g` if `g` takes the same value at any two points of `S`. [RY20, Ch. 1, Definition (monochromatic)]. -/
def CommunicationComplexity.Rectangle.IsMonochromatic (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ x x' y y', (x, y) ∈ S → (x', y') ∈ S → g x y = g x' y'
