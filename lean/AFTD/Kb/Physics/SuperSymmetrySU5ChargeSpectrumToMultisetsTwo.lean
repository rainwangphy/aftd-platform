import AFTD.Prelude

/-!
# SuperSymmetry.SU5.ChargeSpectrum.toMultisetsTwo

Topic: quantum_field_theory   Node: 5686030caafe

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.toMultisetsTwo`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/MinimallyAllowsTerm/OfFinset.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The multisets of cardinality `2` containing elements from a finite set `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓩 : Type} in
/-- The multisets of cardinality `2` containing elements from a finite set `s`. -/
def SuperSymmetry.SU5.ChargeSpectrum.toMultisetsTwo (s : Finset 𝓩) : Multiset (Multiset 𝓩) :=
  let X1 := (s.powersetCard 1).val.map (fun X => X.val.bind (fun x => Multiset.replicate 2 x))
  let X2 := (s.powersetCard 2).val.map fun X => X.val
  X1 + X2
