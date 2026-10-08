import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxSocialWelfare

/-!
# MultipleParameterMechanism.exists_efficientAllocation

Topic: mechanism_design   Node: b6dff700ab22

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.exists_efficientAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists an allocation maximizing reported social welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
/-- There exists an allocation maximizing reported social welfare. -/
lemma MultipleParameterMechanism.exists_efficientAllocation (v : ∀ _ : I, Valuation A ℝ) :
    ∃ a : A, ∀ b : A, socialWelfare v b ≤ socialWelfare v a := by
  classical
  obtain ⟨a, _ha_mem, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset A))
      (H := Finset.univ_nonempty) (f := socialWelfare v)
  refine ⟨a, ?_⟩
  intro b
  have hb : socialWelfare v b ≤ maxSocialWelfare v := by
    exact Finset.le_sup' (socialWelfare v) (Finset.mem_univ b)
  simpa [maxSocialWelfare, ha] using hb
