import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# SingleParameterMechanism.IsMonotone

Topic: mechanism_design   Node: 646db9a3f89a

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.IsMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Monotonicity of the allocation rule. Agent `i`'s allocation is non-decreasing in `i`'s reported type, holding all other reports fixed. This is Myerson's necessary and sufficient condition for DSIC in the single-parameter setting (with quasi-linear utility and the appropriate payment formula). [Myerson 1981; AGT Thm 9.36]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- Monotonicity of the allocation rule. Agent `i`'s allocation is non-decreasing in `i`'s reported type, holding all other reports fixed. This is Myerson's necessary and sufficient condition for DSIC in the single-parameter setting (with quasi-linear utility and the appropriate payment formula). [Myerson 1981; AGT Thm 9.36] -/
def SingleParameterMechanism.IsMonotone [Preorder R] : Prop :=
  ∀ (i : I) (θ θ' : R), θ ≤ θ' →
    ∀ (b : I → R),
      M.allocationRule (Function.update b i θ) i ≤
      M.allocationRule (Function.update b i θ') i
