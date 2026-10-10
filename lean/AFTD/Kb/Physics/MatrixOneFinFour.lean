import AFTD.Prelude

/-!
# Matrix.one_fin_four

Topic: special_relativity   Node: 18af6077bb58

Provenance: formalization of a published result. Source: Physlib, `Matrix.one_fin_four`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/CliffordAlgebra.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.one_fin_four
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Complex in
theorem Matrix.one_fin_four {α} [Zero α] [One α] :
    (1 : Matrix (Fin 4) (Fin 4) α) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :=
  Matrix.etaExpand_eq _ |>.symm
