import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.eval

Topic: combinatorics   Node: e700a079f2c5

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree.eval`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluates a decision tree on an input $x$: a leaf returns its stored bit, and a branch
on variable $i$ follows the high subtree when $x_i$ is \texttt{true} and the low subtree
otherwise.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Evaluate decision tree `T` on input `x`. -/
def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf b,          _  => b
  | .branch i lo hi,  x  => if x i then hi.eval x else lo.eval x
