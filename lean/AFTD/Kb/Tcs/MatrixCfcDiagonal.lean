import AFTD.Prelude

/-!
# Matrix.cfc_diagonal

Topic: quantum   Node: 8f54659e0b56

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.cfc_diagonal`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Matrix.cfc_diagonal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open ComplexOrder in
variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜] in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem Matrix.cfc_diagonal (g : d → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun x ↦ (g x : 𝕜))) = diagonal (RCLike.ofReal ∘ f ∘ g) := by
  --Thanks Aristotle
  have h_self_adjoint : _root_.IsSelfAdjoint (diagonal (fun x => (g x : 𝕜))) := by
      change Matrix.conjTranspose _ = _
      simp [Matrix.conjTranspose]
  --TODO cfc_cont_tac
  rw [cfc, dif_pos ⟨h_self_adjoint, continuousOn_iff_continuous_domRestrict.mpr <| by fun_prop⟩]
  rw [cfcHom_eq_of_continuous_of_map_id]
  rotate_left
  · refine' { .. }
    use fun f ↦ Matrix.diagonal fun x ↦ f ⟨g x, (by
      simpa [algebraMap_eq_diagonal, diagonal_apply] using
        congr_arg (· x x) ·.exists_left_inv.choose_spec
      )⟩
    · simp
    · simp [diagonal, ← Matrix.ext_iff, mul_apply]
      intro x y i j
      split_ifs with h
      · subst h; simp
      · rfl
    · simp
    · simp [diagonal, funext_iff]
      intro x y i j
      split_ifs with h
      · simp
      · simp
    · simp [← ext_iff, diagonal]
      exact fun r i j ↦ rfl
    · simp [← ext_iff, diagonal]
      grind [RCLike.conj_ofReal]
  · dsimp [diagonal]
    continuity
  · simp [diagonal]
  · simp [diagonal]
