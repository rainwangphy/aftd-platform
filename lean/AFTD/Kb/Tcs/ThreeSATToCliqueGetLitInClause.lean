import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueClause3
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral

/-!
# ThreeSATToClique.getLitInClause

Topic: np_completeness   Node: 07301dd9aa0f

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.getLitInClause`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a 3-clause $c$ and a position $p : \mathrm{Fin}\,3$, returns the $p$-th
literal of $c$: $c.l_1$ at position $0$, $c.l_2$ at position $1$, and $c.l_3$ at
position $2$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Extract the literal at position `p` from a 3-clause. -/
def ThreeSATToClique.getLitInClause {V : Type} (c : Clause3 V) : Fin 3 → Literal V
  | ⟨0, _⟩ => c.l1
  | ⟨1, _⟩ => c.l2
  | ⟨2, _⟩ => c.l3
