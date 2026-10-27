import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowProblemSolvable
import AFTD.Kb.GameTheoryEconomics.RowProtocolSolves
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowView
import AFTD.Kb.GameTheoryEconomics.RowViewOfSage
import AFTD.Kb.GameTheoryEconomics.RowMultiset

/-!
# row_solvable_mono

Topic: combinatorial_games   Node: 54d919b26db1

Provenance: helper lemma. arXiv:2610.33032:180

If the anonymous-slip puzzle for S sages in a row with unlabeled seats is solvable with n symbols (RowProblemSolvable S n hS), then it is also solvable with m symbols (RowProblemSolvable S m hS) for any n ≤ m.
-/

/-- Monotonicity of row puzzle solvability in the number of symbols. -/
theorem row_solvable_mono {S n m : ℕ} (hS : 2 ≤ S) (hnm : n ≤ m)
    (h : RowProblemSolvable S n hS) : RowProblemSolvable S m hS := by
  rcases h with ⟨p, hp⟩
  refine ⟨fun v => Fin.castLE hnm (p v), fun x π₁ π₂ hview hmulti => ?_⟩
  apply hp x π₁ π₂ hview
  have hmap (π : Equiv.Perm (Fin S)) :
      rowMultiset hS (fun v => Fin.castLE hnm (p v)) π =
      Multiset.map (Fin.castLE hnm) (rowMultiset hS p π) := by
    dsimp [rowMultiset]
    rw [Multiset.map_map]
    rfl
  apply Multiset.map_injective (Fin.castLE_injective hnm)
  rwa [← hmap, ← hmap]
