import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVertex
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitInClause

/-!
# ThreeSATToClique.getLitAt

Topic: np_completeness   Node: 567a405dede4

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.getLitAt`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a 3-CNF formula $f$ and a vertex $v : \mathtt{CliqueVertex}\,f.\mathtt{length}$,
returns the literal at position $v.l\_idx$ within clause $f[v.c\_idx]$.  The type of
$v$ guarantees the index is always in bounds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The literal named by vertex `v` in formula `f`. The type of `v` carries `f.length` so the index is always in bounds. -/
def ThreeSATToClique.getLitAt {V : Type} (f : Formula3 V) (v : CliqueVertex f.length) : Literal V :=
  getLitInClause (f.get v.c_idx) v.l_idx
