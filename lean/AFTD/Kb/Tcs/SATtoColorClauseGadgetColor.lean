import AFTD.Prelude

/-!
# SATtoColor.clauseGadgetColor

Topic: np_completeness   Node: db4c244575e5

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.clauseGadgetColor`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given the Boolean truth values $a, b, c_3$ of the three literals of a clause,
$\mathrm{clauseGadgetColor}(a, b, c_3, k)$ assigns a color in $\mathrm{Fin}\,3$
to gadget node $k \in \{0,\ldots,5\}$.  In particular, node $5$ always receives
color $1$ (True), and the remaining nodes are colored so that all internal
gadget edges receive distinct colors whenever at least one literal is true.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Coloring of clause gadget nodes given the boolean values of the three literals. -/
def SATtoColor.clauseGadgetColor (a b c3 : Bool) (k : Fin 6) : Fin 3 :=
  let ff3 := !a && !b && !c3
  let ff  := !a && !b
  match k with
  | ⟨5, _⟩ => 1
  | ⟨4, _⟩ => if ff3 then 0 else if ff then 2 else 0
  | ⟨3, _⟩ => if ff3 then 0 else if ff then 0 else 2
  | ⟨2, _⟩ => if ff3 then 0 else if ff then 2 else 1
  | ⟨1, _⟩ => if ff3 then 0 else if ff then 1 else if !b then 0 else 2
  | ⟨0, _⟩ => if ff3 then 0 else if ff then 0 else if !a then 0 else if !b then 2 else 0
