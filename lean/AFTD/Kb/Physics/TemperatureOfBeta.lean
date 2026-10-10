import AFTD.Prelude
import AFTD.Kb.Physics.Temperature
import AFTD.Kb.Physics.ConstantsKB
import AFTD.Kb.Physics.ConstantsKBNonneg
import AFTD.Kb.Physics.TemperatureBeta
import AFTD.Kb.Physics.TemperatureInstCoeNNReal
import AFTD.Kb.Physics.TemperatureInstCoeReal
import AFTD.Kb.Physics.TemperatureInstTopologicalSpace
import AFTD.Kb.Physics.TemperatureInstZero

/-!
# Temperature.ofβ

Topic: statistical_mechanics   Node: bd2c211458cf

Provenance: formalization of a published result. Source: Physlib, `Temperature.ofβ`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Thermodynamics/Temperature/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The temperature associated with a given inverse temperature `β`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Constants in
/-- The temperature associated with a given inverse temperature `β`. -/
noncomputable def Temperature.ofβ (β : ℝ≥0) : Temperature :=
  ⟨⟨1 / (kB * β), div_nonneg zero_le_one (mul_nonneg kB_nonneg β.2)⟩⟩
