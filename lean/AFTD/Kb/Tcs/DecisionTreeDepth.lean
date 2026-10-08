import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.depth

Topic: combinatorics   Node: 66e20d96c67a

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree.depth`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The depth of a decision tree (maximum path length to a leaf): a leaf has depth $0$ and a
branch has depth $1$ plus the maximum of its two subtrees' depths.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Depth of a decision tree (maximum path length to a leaf). [OD14, §3.2] -/
def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _          => 0
  | .branch _ lo hi  => 1 + max lo.depth hi.depth
