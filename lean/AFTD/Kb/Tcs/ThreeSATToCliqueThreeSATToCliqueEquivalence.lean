import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueThreeSATToCliqueCompleteness
import AFTD.Kb.Tcs.ThreeSATToCliqueThreeSATToCliqueSoundness
import AFTD.Kb.Tcs.ThreeSATToCliqueHasClique
import AFTD.Kb.Tcs.ThreeSATToCliqueIs3Satisfiable
import AFTD.Kb.Tcs.ThreeSATToCliqueToCliqueGraph
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.ThreeSAT_to_Clique_equivalence

Topic: np_completeness   Node: af4b435d3a93

Provenance: formalization of a published result. Source: Correctness of the 3-SAT to Clique reduction, as formalized in TCSlib (`ThreeSATToClique.ThreeSAT_to_Clique_equivalence`). Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Correctness of the 3-SAT to Clique reduction. Let $f$ be a 3-CNF formula with $m$ clauses. Then $f$ is satisfiable if and only if its
conflict graph has a clique of size $m$; that is, the graph whose vertices are the
literal positions of $f$, with two positions adjacent exactly when they lie in different
clauses and their literals do not conflict, contains $m$ pairwise-adjacent vertices
precisely when some truth assignment satisfies every clause of $f$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- **Equivalence**: a 3-CNF formula is satisfiable if and only if its conflict graph contains a clique of size equal to the number of clauses. -/
theorem ThreeSATToClique.ThreeSAT_to_Clique_equivalence {V : Type} (f : Formula3 V) :
    is3Satisfiable f ↔ hasClique (toCliqueGraph f) f.length :=
  ⟨ThreeSAT_to_Clique_completeness f, ThreeSAT_to_Clique_soundness f⟩
