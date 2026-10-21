import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunGrundy
import AFTD.Kb.GameTheoryEconomics.RunGrundyAuxEqRunGrundy
import AFTD.Kb.GameTheoryEconomics.RunMoveLegal
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.RunBoundary
import AFTD.Kb.GameTheoryEconomics.RunGrundyAux

/-!
# run_grundy_step

Topic: combinatorial_games   Node: 11b40aaa3b37

Provenance: helper lemma. scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:419

For every k > 0 and boundary conditions α and β, the Grundy value run_grundy k α β is the minimum excluded value of the nim-sums of the Grundy values of the two sub-runs over all legal moves on edges 1 ≤ j ≤ k and orientations δ.
-/

/-- Sprague-Grundy recurrence for the Grundy value of a run of length k > 0. -/
theorem run_grundy_step (k : ℕ) (α β : RunBoundary) (hk : 0 < k) :
    run_grundy k α β =
      nat_mex_list
        ((List.range k).flatMap fun idx =>
          let j := idx + 1
          [RunBoundary.blocked_in, RunBoundary.blocked_out].filterMap fun δ =>
            if run_move_legal k α β j δ then
              some (run_grundy (j - 1) α δ ^^^ run_grundy (k - j) δ β)
            else
              none) := by
  rw [run_grundy]
  rw [run_grundy_aux.eq_2]
  rw [if_neg (by omega : ¬ k = 0)]
  dsimp only
  apply congrArg nat_mex_list
  apply List.flatMap_congr
  intro idx hidx
  simp only [List.mem_range] at hidx
  apply List.filterMap_congr
  intro δ _
  have h1 : run_grundy_aux k (idx + 1 - 1) α δ = run_grundy (idx + 1 - 1) α δ := by
    rw [run_grundy_aux_eq_run_grundy _ _ _ _ (by omega)]
  have h2 : run_grundy_aux k (k - (idx + 1)) δ β = run_grundy (k - (idx + 1)) δ β := by
    rw [run_grundy_aux_eq_run_grundy _ _ _ _ (by omega)]
  rw [h1, h2]
