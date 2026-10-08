import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorLiteral
import AFTD.Kb.Tcs.SATtoColorClause
import AFTD.Kb.Tcs.SATtoColorSat3

/-!
# SATtoColor.EdgeRelation

Topic: np_completeness   Node: 01e027f4859c

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.EdgeRelation`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathrm{EdgeRelation}(f, u, v)$ defines the (undirected) adjacency structure
of the reduction graph.  The edges are:
all pairs of distinct palette nodes;
every literal node to the Base palette node;
$\mathrm{pos}(x)$ to $\mathrm{neg}(x)$ for each variable $x$;
specific pairs of clause gadget nodes within the same clause (encoding two
internal triangles on nodes $\{0,1,2\}$ and $\{3,4,5\}$ plus the bridge
$2$--$3$);
each clause's three literal nodes to gadget nodes $0$, $1$, and $4$
respectively;
and gadget node $5$ of every clause to both the Base and the False palette
nodes.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Edge relation for reduction from 3-SAT to 3-COLORING. -/
def SATtoColor.EdgeRelation {V : Type} (clauses : Sat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  | .palette i, .palette j => i ≠ j
  | .palette 0, .literalNode _ => True
  | .literalNode _, .palette 0 => True
  | .literalNode (.pos x), .literalNode (.neg y) => x = y
  | .literalNode (.neg x), .literalNode (.pos y) => x = y
  | .clauseGadget c1 i, .clauseGadget c2 j =>
      c1 = c2 ∧ c1 ∈ clauses ∧ (
        (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
        (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) ∨
        (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 2) ∨
        (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) ∨ (i = 5 ∧ j = 4)
      )
  | .literalNode z, .clauseGadget c i =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget c i, .literalNode z =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget _ 5, .palette 0 => True
  | .palette 0, .clauseGadget _ 5 => True
  | .clauseGadget _ 5, .palette 2 => True
  | .palette 2, .clauseGadget _ 5 => True
  | _, _ => False
