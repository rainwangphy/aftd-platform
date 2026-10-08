import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVertex
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitAt
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitInClause

/-!
# ThreeSATToClique.getLitAt_mem_clause

Topic: np_completeness   Node: 9e94108bf9ef

Provenance: helper lemma. TCSlib, `ThreeSATToClique.getLitAt_mem_clause`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Vertex literal lies among its clause's three literals. Let $f$ be a 3-CNF formula, let $v$ be a vertex of the conflict graph of $f$, and let
$i$ be a clause index of $f$ such that the clause component of $v$ equals $i$. Then the
literal named by $v$ is one of the three literals $l_1, l_2, l_3$ of the clause $f[i]$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The literal named by vertex `v` with `v.c_idx = i` is one of the three literals of clause `f.get i`. This is used in the soundness proof to route the clique's chosen literal back to the original clause. -/
lemma ThreeSATToClique.getLitAt_mem_clause {V : Type} (f : Formula3 V) (v : CliqueVertex f.length)
    (i : Fin f.length) (h : v.c_idx = i) :
    getLitAt f v ∈ [(f.get i).l1, (f.get i).l2, (f.get i).l3] := by
  subst h
  dsimp [getLitAt]
  rcases hl : v.l_idx with ⟨val, isLt⟩
  rcases val with _ | _ | _ | n
  · simp [getLitInClause]
  · simp [getLitInClause]
  · simp [getLitInClause]
  · omega

-- =============================================================
-- Section 5. Main theorems
-- =============================================================
