import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibDerivativeIndex
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexOrder
import AFTD.Kb.Physics.PhyslibMultiIndexExt
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexOrderZero
import AFTD.Kb.Physics.PhyslibMultiIndexOrderSingle
import AFTD.Kb.Physics.PhyslibMultiIndexOrderIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTailZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementSucc
import AFTD.Kb.Physics.PhyslibMultiIndexToListZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListSingle
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.instFintypeDerivativeIndex

Topic: classical_mechanics   Node: 6b86b0dfad19

Provenance: formalization of a published result. Source: Physlib, `Physlib.instFintypeDerivativeIndex`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/DerivativeIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.instFintypeDerivativeIndex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable instance Physlib.instFintypeDerivativeIndex (d k : ℕ) : Fintype (DerivativeIndex d k) :=
  Fintype.ofInjective
    (fun I : DerivativeIndex d k => fun i : Fin d =>
      ((⟨I.1 i, by
        have hle_order : I.1 i ≤ I.1.order := by
          classical
          unfold Physlib.MultiIndex.order
          simpa using
            (Finset.single_le_sum (fun j _ => Nat.zero_le (I.1 j)) (by simp : i ∈ Finset.univ) :
              I.1 i ≤ ∑ j : Fin d, I.1 j)
        exact Nat.lt_succ_of_le (le_trans hle_order I.2)⟩) : Fin (k + 1)))
    (by
      intro I J h
      apply Subtype.ext
      apply Physlib.MultiIndex.ext
      intro i
      exact congrArg Fin.val (congrFun h i))
