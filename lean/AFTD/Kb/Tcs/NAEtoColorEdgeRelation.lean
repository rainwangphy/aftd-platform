import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorNAEclause
import AFTD.Kb.Tcs.NAEtoColorOutputVertex

/-!
# NAEtoColor.EdgeRelation

Topic: np_completeness   Node: e857978d679f

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.EdgeRelation`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a NAE-SAT instance $\mathit{clauses}$, the directed edge relation on
$\texttt{NAEtoColor.OutputVertex}\;V$ is defined by:
(1) $\mathtt{groundNode}$ is adjacent to every $\mathtt{varNode}$;
(2) $\mathtt{varNode}\;v$ is adjacent to $\mathtt{clauseNode}\;c\;i$ when $v$
is the $i$-th variable of clause $c$;
(3) two clause-gadget nodes $\mathtt{clauseNode}\;c\;i$ and
$\mathtt{clauseNode}\;c\;j$ are adjacent when $c \in \mathit{clauses}$ and
$i \neq j$ (forming a triangle within each clause gadget).
All other pairs are non-adjacent.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Edge relation for reduction from NAE-SAT to 3-COLORING. The edges over this graph are defined as follows: * The ground vertex `⊥` is connected to each variable vertex `x_i`. * For a clause `c_r` containing variables `x_i`, `x_j` and `x_k`, we connect * `x_i`, `x_j`, `x_k` to `c_{r, 1}`, `c_{r, 2}`, `c_{r, 3}` respectively. * `c_{r, 1}`, `c_{r, 2}` and `c_{r,3}` are all interconnected. This is visualized below: ⊥ | +-----+-----+ | | | x_1 x_2 x_3 | | | c_1---c_2---c_3 | | +-----------+ -/
def NAEtoColor.EdgeRelation {V : Type} (clauses : NAESat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  -- Connect ground vertex with every variable node.
  | .groundNode, .varNode _ => True
  | .varNode _, .groundNode => True

  -- Connect variable node to corresponding clause nodes.
  | .varNode v, .clauseNode c i =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)
  | .clauseNode c i, .varNode v =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)

  -- Connect clause gadgets to each other
  | .clauseNode c1 i, .clauseNode c2 j => c1 = c2 ∧ c1 ∈ clauses ∧ i ≠ j

  -- If a pair of vertices doesn't match any of the above patterns, there is no edge.
  | _, _ => False
