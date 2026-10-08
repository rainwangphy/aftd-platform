import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxWelfareWithout

/-!
# MultipleParameterMechanism.exists_withoutAllocation

Topic: mechanism_design   Node: d48473c5558e

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.exists_withoutAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists an allocation maximizing the reported welfare of agents other than `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- There exists an allocation maximizing the reported welfare of agents other than `i`. -/
lemma MultipleParameterMechanism.exists_withoutAllocation (v : ∀ _ : I, Valuation A ℝ) (i : I) :
    ∃ a : A, ∀ b : A, welfareWithout v i b ≤ welfareWithout v i a := by
  classical
  obtain ⟨a, _ha_mem, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset A))
      (H := Finset.univ_nonempty) (f := welfareWithout v i)
  refine ⟨a, ?_⟩
  intro b
  have hb : welfareWithout v i b ≤ maxWelfareWithout v i := by
    exact Finset.le_sup' (welfareWithout v i) (Finset.mem_univ b)
  simpa [maxWelfareWithout, ha] using hb
