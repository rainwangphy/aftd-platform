import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# antitone_mul_of_antitone_nonneg

Topic: quantum   Node: c0c5232d9fa7

Provenance: formalization of a published result. Source: QuantumInfo, `antitone_mul_of_antitone_nonneg`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of nonneg antitone sequences is antitone.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The product of nonneg antitone sequences is antitone. -/
lemma antitone_mul_of_antitone_nonneg {n : ℕ}
    {f g : Fin n → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) :
    Antitone (fun i => f i * g i) := by
  exact fun i j hij => mul_le_mul (hf hij) (hg hij) (hg_nn _) (hf_nn _)
