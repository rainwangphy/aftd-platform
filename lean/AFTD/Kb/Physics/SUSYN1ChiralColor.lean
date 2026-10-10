import AFTD.Prelude

/-!
# SUSY.N1.ChiralColor

Topic: quantum_field_theory   Node: fba612be784d

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.ChiralColor`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The four colours carried by a chiral-sector index: holomorphy (`chiral` versus `anti`, a scalar versus its complex conjugate) crossed with variance (`up` versus `down`, contravariant versus covariant). Carrying both axes here lets the single index type `ι` label the scalars.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
/-- The four colours carried by a chiral-sector index: holomorphy (`chiral` versus `anti`, a scalar versus its complex conjugate) crossed with variance (`up` versus `down`, contravariant versus covariant). Carrying both axes here lets the single index type `ι` label the scalars. -/
inductive SUSY.N1.ChiralColor | chiralUp | chiralDown | antiUp | antiDown
deriving DecidableEq
