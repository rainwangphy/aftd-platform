import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisDropEquiv

/-!
# MinimaxLoomis.sum_split_at

Topic: equilibria   Node: 4adf5b4605bc

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.sum_split_at`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sum-splitting lemma: any function on `J` decomposes as the value at `j₀` plus the sum over `{j // j ≠ j₀}`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Sum-splitting lemma: any function on `J` decomposes as the value at `j₀` plus the sum over `{j // j ≠ j₀}`. -/
theorem MinimaxLoomis.sum_split_at [DecidableEq J] (j₀ : J) (f : J → ℝ) :
    ∑ j : J, f j = f j₀ + ∑ j' : {j : J // j ≠ j₀}, f j'.val := by
  have hbij : ∑ j : J, f j =
      ∑ o : Option {j : J // j ≠ j₀}, f ((dropEquiv j₀).symm o) :=
    Fintype.sum_equiv (dropEquiv j₀) f (fun o => f ((dropEquiv j₀).symm o))
      (fun j => by simp)
  rw [hbij, Fintype.sum_option]
  rfl
