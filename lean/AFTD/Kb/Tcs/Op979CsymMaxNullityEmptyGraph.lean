import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCsymMaxNullity
import AFTD.Kb.Tcs.IsCsymMatrix

/-!
# op_979_csym_max_nullity_empty_graph

Topic: graphs   Node: 98966e600098

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 6, Example 6.2

For the edgeless graph (the empty graph bot) on a finite vertex set V, the combinatorially symmetric maximum nullity equals the number of vertices |V|.
-/

/-- For the edgeless graph on a finite vertex set V, N(⊥) = |V|. -/
theorem op_979_csym_max_nullity_empty_graph
    {V : Type*} [Fintype V] [DecidableEq V] :
    simple_graph_csym_max_nullity (⊥ : SimpleGraph V) = Fintype.card V := by
  classical
  unfold simple_graph_csym_max_nullity
  set S : Set ℕ := { k : ℕ | ∃ A : Matrix V V ℝ,
    is_csym_matrix (⊥ : SimpleGraph V) A ∧ Module.finrank ℝ A.mulVecLin.ker = k } with hSdef
  have hmem : Fintype.card V ∈ S := by
    refine ⟨0, ?_, ?_⟩
    · exact ⟨fun i j => by simp, fun i j _ => by simp⟩
    · rw [Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top]
      exact Module.finrank_fintype_fun_eq_card ℝ
  have hle : ∀ b ∈ S, b ≤ Fintype.card V := by
    rintro b ⟨A, -, hb⟩
    rw [← hb]
    calc Module.finrank ℝ A.mulVecLin.ker
        ≤ Module.finrank ℝ (V → ℝ) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card ℝ
  have hbdd : BddAbove S := ⟨Fintype.card V, hle⟩
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hle) (le_csSup hbdd hmem)
