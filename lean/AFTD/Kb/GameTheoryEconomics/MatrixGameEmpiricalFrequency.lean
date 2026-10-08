import AFTD.Prelude

/-!
# MatrixGame.empiricalFrequency

Topic: equilibria   Node: d54a2e9007e8

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.empiricalFrequency`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/FictitiousPlay.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Empirical frequency** of the first `n` pure actions of a sequence `a : ℕ → I`. For `n = 0` we fall back to the uniform distribution so the function is total; the FP statements always require `0 < n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
/-- **Empirical frequency** of the first `n` pure actions of a sequence `a : ℕ → I`. For `n = 0` we fall back to the uniform distribution so the function is total; the FP statements always require `0 < n`. -/
noncomputable def MatrixGame.empiricalFrequency (a : ℕ → I) (n : ℕ) : stdSimplex ℝ I :=
  if hn : 0 < n then
    ⟨fun i => (((Finset.range n).filter (fun s => a s = i)).card : ℝ) / n, by
      refine ⟨fun i => ?_, ?_⟩
      · positivity
      · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hsum_div :
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ) / n)
              = (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ)) / n := by
          rw [← Finset.sum_div]
        rw [hsum_div]
        have hcount :
            (∑ i, ((Finset.range n).filter (fun s => a s = i)).card)
              = (Finset.range n).card := by
          rw [← Finset.card_eq_sum_card_fiberwise (f := a)
                (s := Finset.range n) (t := Finset.univ)
                (fun s _ => Finset.mem_univ (a s))]
        have hsum_real :
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ))
              = (n : ℝ) := by
          calc
            (∑ i, (((Finset.range n).filter (fun s => a s = i)).card : ℝ))
                = ((∑ i, ((Finset.range n).filter (fun s => a s = i)).card : ℕ) : ℝ) := by
                  push_cast; rfl
            _ = ((Finset.range n).card : ℝ) := by exact_mod_cast hcount
            _ = (n : ℝ) := by rw [Finset.card_range]
        rw [hsum_real, div_self hn_pos.ne']⟩
  else
    ⟨fun _ => (Fintype.card I : ℝ)⁻¹, by
      have hcard : 0 < Fintype.card I := Fintype.card_pos
      have hpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hcard
      refine ⟨fun _ => le_of_lt (inv_pos.mpr hpos), ?_⟩
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp⟩
