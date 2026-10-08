import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueCliqueVertex
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueGetLitAt
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflict
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflictSymm
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.toCliqueGraph

Topic: np_completeness   Node: f4f79b98b6a2

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.toCliqueGraph`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The conflict graph of a 3-CNF formula $f$ is the simple graph on vertex set
$\mathtt{CliqueVertex}\,f.\mathtt{length}$ in which two vertices $u$ and $v$ are
adjacent if and only if they come from \emph{different} clauses ($u.c\_idx \ne
v.c\_idx$) and their respective literals do not conflict.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The conflict graph of a 3-CNF formula `f`: * **vertices**: `CliqueVertex f.length`, i.e. pairs `(clause index, literal position)`. * **edges**: two vertices are adjacent iff they belong to *different* clauses and their respective literals do not conflict. -/
def ThreeSATToClique.toCliqueGraph {V : Type} (f : Formula3 V) : SimpleGraph (CliqueVertex f.length) where
  Adj u v := u.c_idx ≠ v.c_idx ∧ ¬ (literalsConflict (getLitAt f u) (getLitAt f v))
  symm := ⟨fun u v => by
    intro ⟨hne, hnc⟩
    exact ⟨hne.symm, by rwa [literalsConflict_symm] at hnc⟩⟩
  loopless := ⟨fun u => by simp⟩
