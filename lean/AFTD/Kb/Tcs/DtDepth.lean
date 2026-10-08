import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeBuildFull
import AFTD.Kb.Tcs.DecisionTreeBuildFullDepth
import AFTD.Kb.Tcs.DecisionTreeBuildFullEval
import AFTD.Kb.Tcs.DecisionTreeDepth
import AFTD.Kb.Tcs.DecisionTreeEval

/-!
# dtDepth

Topic: combinatorics   Node: 1e7f24643b08

Provenance: formalization of a published result. Source: TCSlib, `dtDepth`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The decision-tree depth of $f : (\mathrm{Fin}\,n \to \mathrm{Bool}) \to
\mathrm{Bool}$ is the least $d$ such that some decision tree of depth at most $d$
computes $f$; it is well defined since the full tree computes $f$ at depth $n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The minimum decision-tree depth to compute `f : (Fin n → Bool) → Bool`. [OD14, §3.2] Formally: `min { T.depth | T computes f }` = `Nat.sInf {d | ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x}`. -/
noncomputable def dtDepth {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
    ⟨n, DecisionTree.buildFull f 0 (fun _ => false),
     DecisionTree.buildFull_depth f 0 (Nat.zero_le n) _,
     fun x => DecisionTree.buildFull_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
