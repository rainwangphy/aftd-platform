import AFTD.Prelude

/-!
# ThreeSATToClique.hasClique

Topic: np_completeness   Node: a2e128e3f5a9

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.hasClique`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A graph $G$ on vertex type $V$ \emph{has a $k$-clique} if there exists a finite set
$s \subseteq V$ of $k$ vertices that are pairwise adjacent in $G$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A graph `G` has a **`k`-clique** if there exists a set of `k` pairwise adjacent vertices. -/
def ThreeSATToClique.hasClique {V : Type} (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ (s : Finset V), s.card = k ∧ G.IsClique s

-- =============================================================
-- Section 4. Auxiliary lemmas
-- =============================================================
