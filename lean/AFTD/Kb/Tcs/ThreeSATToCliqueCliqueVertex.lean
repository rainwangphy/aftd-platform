import AFTD.Prelude

/-!
# ThreeSATToClique.CliqueVertex

Topic: np_completeness   Node: a9613378dd8d

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.CliqueVertex`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A vertex of the conflict graph for a formula with $m$ clauses is a pair
$\langle c\_idx, l\_idx \rangle$ where $c\_idx : \mathrm{Fin}\,m$ is a clause index
and $l\_idx : \mathrm{Fin}\,3$ is a literal position within that clause.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A vertex of the conflict graph names a literal by its clause index `c_idx : Fin m` and its position `l_idx : Fin 3` within that clause. -/
structure ThreeSATToClique.CliqueVertex (m : Nat) where
  c_idx : Fin m
  l_idx : Fin 3
deriving DecidableEq
