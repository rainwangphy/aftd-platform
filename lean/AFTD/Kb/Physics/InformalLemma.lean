import AFTD.Prelude

/-!
# InformalLemma

Topic: classical_mechanics   Node: 6cbcccb2aba9

Provenance: formalization of a published result. Source: Physlib, `InformalLemma`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Meta/Informal/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure representing an informal lemma.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure representing an informal lemma. -/
structure InformalLemma where
  /-- The names of top-level commands we expect this lemma to depend on. -/
  deps : List Lean.Name
  /-- The tag of the informal lemma. This should be unique amongst informal results
    and todo items. -/
  tag : String
