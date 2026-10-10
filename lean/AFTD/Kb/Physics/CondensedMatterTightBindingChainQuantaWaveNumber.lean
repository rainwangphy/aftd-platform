import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain

/-!
# CondensedMatter.TightBindingChain.QuantaWaveNumber

Topic: condensed_matter   Node: ddcd3033ab1b

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.QuantaWaveNumber`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter in
open InnerProductSpace in
variable (T : TightBindingChain) in
/-- The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone. -/
def CondensedMatter.TightBindingChain.QuantaWaveNumber : Set ℝ := {x | (∃ n : Fin T.N,
    2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x)}
