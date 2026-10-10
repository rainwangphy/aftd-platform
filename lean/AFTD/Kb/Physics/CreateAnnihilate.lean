import AFTD.Prelude

/-!
# CreateAnnihilate

Topic: quantum_field_theory   Node: 8f4698677662

Provenance: formalization of a published result. Source: Physlib, `CreateAnnihilate`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `CreateAnnihilate` is the type containing two elements `create` and `annihilate`. This type is used to specify if an operator is a creation, or annihilation, operator or the sum thereof or integral thereof etc.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `CreateAnnihilate` is the type containing two elements `create` and `annihilate`. This type is used to specify if an operator is a creation, or annihilation, operator or the sum thereof or integral thereof etc. -/
inductive CreateAnnihilate where
  | create : CreateAnnihilate
  | annihilate : CreateAnnihilate
deriving Inhabited, BEq, DecidableEq
