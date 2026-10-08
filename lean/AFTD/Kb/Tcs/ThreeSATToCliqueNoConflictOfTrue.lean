import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueEvalLiteral
import AFTD.Kb.Tcs.ThreeSATToCliqueAssignment
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflict
import AFTD.Kb.Tcs.ThreeSATToCliqueLiteralsConflictSymm

/-!
# ThreeSATToClique.no_conflict_of_true

Topic: np_completeness   Node: 35104342211a

Provenance: helper lemma. TCSlib, `ThreeSATToClique.no_conflict_of_true`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

True literals never conflict. Let $\alpha$ be a truth assignment on a set $V$ of variables, and let $\ell_1,\ell_2$ be
literals over $V$, each of the form $\mathrm{pos}\,v$ (the variable $v$) or
$\mathrm{neg}\,v$ (its negation). If both $\ell_1$ and $\ell_2$ evaluate to true under
$\alpha$, then they do not conflict; that is, they are not the positive and negative
occurrences of one and the same variable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Two simultaneously true literals cannot conflict: if `α` makes both `l1` and `l2` true, they cannot be complementary. *Proof*: complementarity forces `α v` and `¬ α v` for the same `v`. -/
lemma ThreeSATToClique.no_conflict_of_true {V : Type} (α : Assignment V) (l1 l2 : Literal V)
    (h1 : evalLiteral α l1) (h2 : evalLiteral α l2) : ¬ literalsConflict l1 l2 := by
  intro hc
  cases l1 <;> cases l2 <;> simp only [literalsConflict, evalLiteral] at hc h1 h2
  · -- l1 = .pos v1, l2 = .neg v2, conflict forces v1 = v2.
    rw [hc] at h1; exact h2 h1
  · -- l1 = .neg v1, l2 = .pos v2, conflict forces v1 = v2.
    rw [hc] at h1; exact h1 h2
