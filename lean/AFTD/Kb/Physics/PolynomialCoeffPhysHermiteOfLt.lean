import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSuccSucc
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne

/-!
# Polynomial.coeff_physHermite_of_lt

Topic: classical_mechanics   Node: fe54ed05e9e3

Provenance: formalization of a published result. Source: Physlib, `Polynomial.coeff_physHermite_of_lt`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.coeff_physHermite_of_lt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
lemma Polynomial.coeff_physHermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (physHermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, add_right_comm, show n + k + 1 + 2 = n + (k + 2) + 1 by ring,
      ih k, ih (k + 2)]
    simp
