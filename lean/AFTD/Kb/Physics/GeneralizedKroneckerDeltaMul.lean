import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaSymm
import AFTD.Kb.Physics.KroneckerDeltaSumMul
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm

/-!
# generalizedKroneckerDelta_mul

Topic: classical_mechanics   Node: f36a1a170a20

Provenance: formalization of a published result. Source: Physlib, `generalizedKroneckerDelta_mul`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Contraction.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of two Levi-Civita-type symbols is a generalized Kronecker delta: `δ^{μ}_{·} · δ^{ν}_{·} = δ^{μ}_{ν}`, where each single factor is a Kronecker matrix against the identity. This is the Lean form of `ε^{μ₁…μₙ} ε_{ν₁…νₙ} = δ^{μ₁…μₙ}_{ν₁…νₙ}`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open KroneckerDelta in
open Matrix in
variable {α : Type} [DecidableEq α] [Fintype α] in
/-- The product of two Levi-Civita-type symbols is a generalized Kronecker delta: `δ^{μ}_{·} · δ^{ν}_{·} = δ^{μ}_{ν}`, where each single factor is a Kronecker matrix against the identity. This is the Lean form of `ε^{μ₁…μₙ} ε_{ν₁…νₙ} = δ^{μ₁…μₙ}_{ν₁…νₙ}`. -/
lemma generalizedKroneckerDelta_mul (μ ν : α → α) :
    generalizedKroneckerDelta μ id * generalizedKroneckerDelta ν id
      = generalizedKroneckerDelta μ ν := by
  rw [show generalizedKroneckerDelta ν id
        = (Matrix.of fun i j => ((kroneckerDelta (ν i) (id j) : ℕ) : ℤ)).det from rfl,
    ← Matrix.det_transpose,
    show generalizedKroneckerDelta μ id
        = (Matrix.of fun i j => ((kroneckerDelta (μ i) (id j) : ℕ) : ℤ)).det from rfl,
    ← Matrix.det_mul,
    show generalizedKroneckerDelta μ ν
        = (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)).det from rfl]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.transpose_apply, id_eq, ← Nat.cast_mul]
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_congr rfl fun k _ => by rw [KroneckerDelta.symm (ν j) k]]
  exact KroneckerDelta.sum_mul (μ i) (ν j)
