import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxMinimaxPos

/-!
# Minimax.minimax

Topic: equilibria   Node: 0dee90ee43b6

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.minimax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Ordered-field von Neumann minimax.** Every finite two-player zero-sum game over a linearly ordered field has a value and optimal mixed strategies.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] in
/-- **Ordered-field von Neumann minimax.** Every finite two-player zero-sum game over a linearly ordered field has a value and optimal mixed strategies. -/
theorem Minimax.minimax (A : I → J → 𝕜) :
    ∃ (x : I → 𝕜) (y : J → 𝕜) (v : 𝕜),
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ (∀ j, 0 ≤ y j) ∧ (∑ j, y j = 1) ∧
      (∀ j, v ≤ ∑ i, x i * A i j) ∧ (∀ i, ∑ j, A i j * y j ≤ v) := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty I›; obtain ⟨j0⟩ := ‹Nonempty J›
  set c : 𝕜 := 1 - Finset.inf' Finset.univ ⟨(i0, j0), Finset.mem_univ _⟩
    (fun r : I × J => A r.1 r.2) with hc
  have hApos : ∀ i j, 0 < A i j + c := by
    intro i j
    have hle : Finset.inf' Finset.univ ⟨(i0, j0), Finset.mem_univ _⟩
        (fun r : I × J => A r.1 r.2) ≤ A i j :=
      Finset.inf'_le _ (Finset.mem_univ (i, j))
    rw [hc]; linarith
  obtain ⟨x, y, v, hxnn, hxsum, hynn, hysum, hxA, hAy⟩ :=
    minimax_pos (fun i j => A i j + c) hApos
  refine ⟨x, y, v - c, hxnn, hxsum, hynn, hysum, ?_, ?_⟩
  · intro j
    have h := hxA j
    rw [show (∑ i, x i * (A i j + c)) = (∑ i, x i * A i j) + c from by
        rw [show (∑ i, x i * (A i j + c)) = ∑ i, (x i * A i j + x i * c) from
          Finset.sum_congr rfl (fun i _ => by ring), Finset.sum_add_distrib,
          ← Finset.sum_mul, hxsum, one_mul]] at h
    linarith
  · intro i
    have h := hAy i
    rw [show (∑ j, (A i j + c) * y j) = (∑ j, A i j * y j) + c from by
        rw [show (∑ j, (A i j + c) * y j) = ∑ j, (A i j * y j + c * y j) from
          Finset.sum_congr rfl (fun j _ => by ring), Finset.sum_add_distrib,
          ← Finset.mul_sum, hysum, mul_one]] at h
    linarith
