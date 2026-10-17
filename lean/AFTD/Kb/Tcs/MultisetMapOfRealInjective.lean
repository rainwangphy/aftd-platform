import AFTD.Prelude
import AFTD.Kb.Tcs.Mixable

/-!
# multiset_map_ofReal_injective

Topic: quantum   Node: 4a02b9d04289

Provenance: formalization of a published result. Source: QuantumInfo, `multiset_map_ofReal_injective`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/VonNeumann.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mapping `RCLike.ofReal` over a multiset is injective.
-/

set_option quotPrecheck false
open Mixable
local notation p "[" x₁:80 "↔" x₂ "]" => mix p x₁ x₂
local notation p "[" x₁:80 "↔" x₂ ":" M "]" => mix (inst := M) p x₁ x₂

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
/-- Mapping `RCLike.ofReal` over a multiset is injective. -/
lemma multiset_map_ofReal_injective {R : Type*} [RCLike R] {M N : Multiset ℝ} :
    M.map (RCLike.ofReal : ℝ → R) = N.map RCLike.ofReal ↔ M = N := by
  exact ⟨fun h ↦ by simpa using congr(($h).map RCLike.re), fun h ↦ by rw [h]⟩
