import AFTD.Prelude

/-!
# Matrix.rank_add_le

Topic: communication   Node: e7b45a4342a9

Provenance: helper lemma. TCSlib, `Matrix.rank_add_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Subadditivity of matrix rank. Let $X$ be any index set and $Y$ a finite index set, and let $A, B \in \bbr^{X \times
Y}$ be real matrices with rows indexed by $X$ and columns indexed by $Y$. Then
\[
  \mathrm{rank}(A + B) \le \mathrm{rank}(A) + \mathrm{rank}(B).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Matrix rank is subadditive: `rank (A + B) ≤ rank A + rank B` [RY20, Fact 2.3]. Stated for real matrices only; candidate for upstreaming to Mathlib. -/
theorem Matrix.rank_add_le {X Y : Type*} [Fintype Y]
    (A B : Matrix X Y ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank; rw [Matrix.mulVecLin_add]
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  exact LinearMap.range_add_le _ _
