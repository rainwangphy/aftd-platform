import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# rpow_antitone_of_nonneg_antitone

Topic: quantum   Node: 3a306d805cfa

Provenance: formalization of a published result. Source: QuantumInfo, `rpow_antitone_of_nonneg_antitone`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Raising nonneg antitone sequences to a positive power preserves antitonicity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Raising nonneg antitone sequences to a positive power preserves antitonicity. -/
lemma rpow_antitone_of_nonneg_antitone {n : ℕ}
    {f : Fin n → ℝ} (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    {r : ℝ} (hr : 0 < r) :
    Antitone (fun i => f i ^ r) := by
  exact fun i j hij => Real.rpow_le_rpow (hf_nn _) (hf hij) hr.le
