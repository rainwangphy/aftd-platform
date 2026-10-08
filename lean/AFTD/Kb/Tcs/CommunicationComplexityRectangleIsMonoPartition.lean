import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Rectangle.IsMonoPartition

Topic: communication   Node: 7665ea91971c

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Rectangle.IsMonoPartition`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A collection $\mathcal{P}$ of subsets of $X \times Y$ is a \emph{monochromatic
rectangle partition} for $g : X \to Y \to \alpha$ if every member of
$\mathcal{P}$ is a rectangle, every member is monochromatic for $g$, the members
cover all of $X \times Y$, and distinct members are disjoint.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A set of sets is a monochromatic rectangle partition of `X × Y` with respect to `g` if every member is a rectangle, every member is monochromatic for `g`, the members cover `X × Y`, and distinct members are disjoint. [RY20, Thm 1.7] (the notion of a partition of `X × Y` into monochromatic rectangles). -/
def CommunicationComplexity.Rectangle.IsMonoPartition
    (Part : Set (Set (X × Y))) (g : X → Y → α) : Prop :=
  (∀ R ∈ Part, IsRectangle R) ∧
  (∀ R ∈ Part, IsMonochromatic R g) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)
