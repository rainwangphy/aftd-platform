import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TT
import AFTD.Kb.GameTheoryEconomics.TTFunlike
import AFTD.Kb.GameTheoryEconomics.TTFinite
import AFTD.Kb.GameTheoryEconomics.TTInhabited

/-!
# TTtostdSimplex

Topic: general_equilibrium   Node: 60faeb126a7e

Provenance: formalization of a published result. Source: EconCSLib, `TTtostdSimplex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TTtostdSimplex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable (n l : ℕ+) (i : Fin n) in
variable {n l} in
noncomputable def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
  ⟩
