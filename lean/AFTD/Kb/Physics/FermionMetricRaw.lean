import AFTD.Prelude

/-!
# Fermion.metricRaw

Topic: special_relativity   Node: 560bd44a7388

Provenance: formalization of a published result. Source: Physlib, `Fermion.metricRaw`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/Metric.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The raw `2x2` matrix corresponding to the metric for fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open CategoryTheory.MonoidalCategory in
/-- The raw `2x2` matrix corresponding to the metric for fermions. -/
noncomputable def Fermion.metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
