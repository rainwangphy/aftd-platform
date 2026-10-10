import AFTD.Prelude

/-!
# EuclideanGroup

Topic: classical_mechanics   Node: 7eaede3a8e78

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An n-dimensional `Euclidean group` is a group of rotations, reflections, and translations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An n-dimensional `Euclidean group` is a group of rotations, reflections, and translations. -/
@[ext]
structure EuclideanGroup (n : ℕ) where
  /-- The translation part of a Euclidean transformation. -/
  translation : EuclideanSpace ℝ (Fin n)
  /-- The orthogonal linear part of a Euclidean transformation. -/
  linear : Matrix.orthogonalGroup (Fin n) ℝ
