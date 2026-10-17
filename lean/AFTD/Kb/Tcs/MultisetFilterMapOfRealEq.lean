import AFTD.Prelude

/-!
# multiset_filter_map_ofReal_eq

Topic: quantum   Node: bcfc28becbd9

Provenance: formalization of a published result. Source: QuantumInfo, `multiset_filter_map_ofReal_eq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Filtering non-zero elements commutes with mapping `RCLike.ofReal` for multisets.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace in
/-- Filtering non-zero elements commutes with mapping `RCLike.ofReal` for multisets. -/
lemma multiset_filter_map_ofReal_eq {R : Type*} [RCLike R] (M : Multiset ℝ) :
    (M.map (RCLike.ofReal : ℝ → R)).filter (· ≠ 0) = (M.filter (· ≠ 0)).map RCLike.ofReal := by
  simp [Multiset.filter_map]

/-
The non-zero roots of the characteristic polynomial are the non-zero eigenvalues mapped
to complex numbers.
-/
