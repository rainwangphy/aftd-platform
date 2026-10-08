import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Rectangle.IsFoolingSet

Topic: communication   Node: ac305b0c0694

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Rectangle.IsFoolingSet`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A set $S \subseteq X \times Y$ is a \emph{fooling set} for $g : X \to Y \to \alpha$
if every monochromatic rectangle with respect to $g$ contains at most one point
of $S$, i.e., $S \cap R$ is a subsingleton for every rectangle $R$ that is
monochromatic for $g$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A set `S ⊆ X × Y` is a fooling set for `g` if every monochromatic rectangle with respect to `g` contains at most one point of `S`. [Rou16, §4.2.5 Definition (fooling set)]. Deviation: Rou16 define a fooling set by the two conditions "`g` is constant on `S`" and "for distinct points of `S`, one of the two mixed pairs has a different `g`-value"; the definition here is the consequence those conditions are used for (every monochromatic rectangle meets `S` in at most one point), which is all the counting bound needs. -/
def CommunicationComplexity.Rectangle.IsFoolingSet (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ R : Set (X × Y), IsRectangle R → IsMonochromatic R g →
    (S ∩ R).Subsingleton
