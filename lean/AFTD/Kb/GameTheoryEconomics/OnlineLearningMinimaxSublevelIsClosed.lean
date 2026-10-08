import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMinimaxSublevel

/-!
# OnlineLearning.minimaxSublevel_isClosed

Topic: equilibria   Node: 0f526c560a48

Provenance: helper lemma. TCSlib, `OnlineLearning.minimaxSublevel_isClosed`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Closedness of the minimax sublevel set. Let $X \subseteq \bbr$ be a closed set, let $f\colon \bbr \times \bbr \to \bbr$ be a
payoff function, and fix a column point $y \in \bbr$ and a threshold $c \in \bbr$. If
the map $x \mapsto f(x,y)$ is continuous on $X$, then the minimax sublevel set
$\mathrm{sublevel}(X,f,y,c) = X \cap \{x \in \bbr : f(x,y) \le c\}$ is closed.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The sublevel set is closed when `X` is closed and the payoff is continuous on `X` in the row variable. -/
lemma OnlineLearning.minimaxSublevel_isClosed {X : Set ℝ} {f : ℝ → ℝ → ℝ} {y c : ℝ}
    (hX : IsClosed X) (hf : ContinuousOn (fun x => f x y) X) :
    IsClosed (minimaxSublevel X f y c) := by
  simpa [minimaxSublevel, Set.preimage, Set.Iic] using
    hf.preimage_isClosed_of_isClosed hX (isClosed_Iic : IsClosed (Set.Iic c))
