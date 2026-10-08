import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SkewSymmetricOptimal

/-!
# Minimax.skew_optimal

Topic: equilibria   Node: 082c6b2d547e

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.skew_optimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`SkewSymmetric.optimal` transported to an arbitrary nonempty finite index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- `SkewSymmetric.optimal` transported to an arbitrary nonempty finite index. -/
theorem Minimax.skew_optimal {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    (S : K → K → 𝕜) (hS : ∀ k l, S k l = - S l k) :
    ∃ z : K → 𝕜, (∀ k, 0 ≤ z k) ∧ (∑ k, z k = 1) ∧ (∀ l, 0 ≤ ∑ k, z k * S k l) := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  haveI : NeZero (Fintype.card K) := ⟨Fintype.card_ne_zero⟩
  set S' : Fin (Fintype.card K) → Fin (Fintype.card K) → 𝕜 :=
    fun a b => S (e.symm a) (e.symm b) with hS'
  obtain ⟨z', hz'_nn, hz'_sum, hz'_col⟩ :=
    SkewSymmetric.optimal S' (fun a b => hS _ _)
  refine ⟨fun k => z' (e k), fun k => hz'_nn _, ?_, ?_⟩
  · rw [Equiv.sum_comp e z']; exact hz'_sum
  · intro l
    have h := hz'_col (e l)
    have heq : (∑ k, z' (e k) * S k l) = ∑ a, z' a * S' a (e l) := by
      rw [← Equiv.sum_comp e (fun a => z' a * S' a (e l))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hS', Equiv.symm_apply_apply]
    rw [heq]; exact h
