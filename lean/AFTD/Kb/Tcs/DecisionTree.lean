import AFTD.Prelude

/-!
# DecisionTree

Topic: combinatorics   Node: d85bfd968e73

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree`. Lean proof by Hydroxyi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/DecisionTree.lean (Copyright (c) 2026 TCSlib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A decision tree on $n$ Boolean variables: a leaf $\mathtt{leaf}\,b$ outputs $b$,
and a branch $\mathtt{branch}\,i\,lo\,hi$ queries variable $i$, following $lo$ on
false and $hi$ on true.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A decision tree on `n` Boolean variables. [OD14, Def 3.13] - `leaf b`: output `b`. - `branch i lo hi`: query variable `i`; follow `lo` on `false`, `hi` on `true`. -/
inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n
