import AFTD.Prelude

/-!
# Cslib.Logic.Modal.Model

Topic: proof_theory   Node: eea50a977219

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.Modal.Model`. Lean proof by Fabrizio Montesi, Marianna Girlando, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Modal/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A model consists of a relation between worlds `r` and a valuation `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A model consists of a relation between worlds `r` and a valuation `v`. -/
structure Cslib.Logic.Modal.Model (World : Type*) (Atom : Type*) where
  /-- World accessibility relation. -/
  r : World → World → Prop
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop
