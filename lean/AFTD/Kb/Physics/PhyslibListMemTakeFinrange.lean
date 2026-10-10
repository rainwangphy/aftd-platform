import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibDistributionPowOneMul
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointSchemeSpec
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne
import AFTD.Kb.GameTheoryEconomics.QuotaPopulationMonotoneIncompatibleFourStatesCommonHouse

/-!
# Physlib.List.mem_take_finrange

Topic: classical_mechanics   Node: 1707f1f2ca86

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.mem_take_finrange`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.mem_take_finrange
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open _root_.Physlib.Fin in
variable {n : Nat} in
set_option maxHeartbeats 350000 in
lemma Physlib.List.mem_take_finrange : (n m : ℕ) → (a : Fin n) → a ∈ List.take m (List.finRange n) ↔ a.val < m
  | 0, m, a => Fin.elim0 a
  | n+1, 0, a => by
    simp
  | n +1, m + 1, ⟨0, h⟩ => by
    simp [List.finRange_succ]
  | n +1, m + 1, ⟨i + 1, h⟩ => by
    simp only [List.finRange_succ, List.take_succ_cons, List.mem_cons, Fin.ext_iff, Fin.val_zero,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or, add_lt_add_iff_right]
    rw [← List.map_take, @List.mem_map]
    apply Iff.intro
    · intro h
      obtain ⟨a, ha⟩ := h
      rw [mem_take_finrange n m a, Fin.ext_iff] at ha
      simp_all only [Fin.val_succ, add_left_inj]
      omega
    · intro h1
      use ⟨i, Nat.succ_lt_succ_iff.mp h⟩
      simp only [Fin.succ_mk, and_true]
      rwa [mem_take_finrange n m ⟨i, Nat.succ_lt_succ_iff.mp h⟩]
