import AFTD.Prelude
import AFTD.Kb.Tcs.GridBoxFreeMax
import AFTD.Kb.Tcs.GridBoxFree
import AFTD.Kb.Tcs.GridBoxFreeOfLe

/-!
# grid_box_free_max_eq_fifty_of_not_exists_fifty_one

Topic: combinatorics   Node: b8c24939bd61

Provenance: helper lemma. arXiv:2611.19635 (Constructive and computational methods for extremal and near-extremal box colorings), Sec. 6

If the grid $[5] \times [7] \times [50]$ admits a box-free $2$-coloring and $[5] \times [7] \times [51]$ admits no box-free $2$-coloring, then $N(5, 7) = 50$.
-/

/-- If 50 layers are colorable but 51 are not, then N(5, 7) = 50. -/
theorem grid_box_free_max_eq_fifty_of_not_exists_fifty_one (h50 : ∃ f : Fin 5 → Fin 7 → Fin 50 → Bool, grid_box_free f) (h51 : ¬ ∃ f : Fin 5 → Fin 7 → Fin 51 → Bool, grid_box_free f) : grid_box_free_max 5 7 = 50 := by
  have hg : IsGreatest {c : ℕ | ∃ f : Fin 5 → Fin 7 → Fin c → Bool, grid_box_free f} 50 := by
    refine ⟨h50, ?_⟩
    intro c hc
    rcases hc with ⟨f, hf⟩
    by_contra! hgt
    have h51_ex : ∃ f' : Fin 5 → Fin 7 → Fin 51 → Bool, grid_box_free f' :=
      ⟨fun x y z => f x y (z.castLE hgt), grid_box_free_of_le hgt hf⟩
    exact h51 h51_ex
  exact hg.csSup_eq
