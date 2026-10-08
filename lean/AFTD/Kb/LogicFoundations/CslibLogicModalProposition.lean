import AFTD.Prelude

/-!
# Cslib.Logic.Modal.Proposition

Topic: proof_theory   Node: e9c61e3f1b59

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.Modal.Proposition`. Lean proof by Fabrizio Montesi, Marianna Girlando, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Modal/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Propositions. -/
inductive Cslib.Logic.Modal.Proposition (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Negation. -/
  | not (φ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Possibility. -/
  | diamond (φ : Proposition Atom)
