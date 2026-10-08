import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankRectMatrix
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Deterministic.Rank.rank_rectMatrix_le_one

Topic: communication   Node: 9dd96641c5f1

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Rank.rank_rectMatrix_le_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Combinatorial rectangles have rank-one indicator matrices. Let $X$ be any set and $Y$ a finite set, and let $R \subseteq X \times Y$ be a
rectangle, meaning $R = A \times B$ for some $A \subseteq X$ and $B \subseteq Y$. Let
$M_R \in \bbr^{X \times Y}$ be its indicator matrix, with $(M_R)_{x,y} = 1$ when $(x,y)
\in R$ and $(M_R)_{x,y} = 0$ otherwise. Then $\mathrm{rank}(M_R) \le 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The indicator matrix of a combinatorial rectangle `R = A ×ˢ B` has rank at most `1`, since it is the outer product of the indicator vectors of `A` and `B`. -/
theorem CommunicationComplexity.Deterministic.Rank.rank_rectMatrix_le_one {X Y : Type*} [Fintype Y]
    (R : Set (X × Y)) (hR : Rectangle.IsRectangle R) :
    (rectMatrix R).rank ≤ 1 := by
  classical
  obtain ⟨A, B, rfl⟩ := hR
  suffices rectMatrix (A ×ˢ B) =
      Matrix.vecMulVec (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun y => if y ∈ B then (1 : ℝ) else 0) by
    rw [this]; exact Matrix.rank_vecMulVec_le _ _
  ext x y; simp only [rectMatrix, Matrix.of_apply, Matrix.vecMulVec, Set.mem_prod_eq]
  cases Classical.em (x ∈ A) <;> cases Classical.em (y ∈ B) <;> simp_all
