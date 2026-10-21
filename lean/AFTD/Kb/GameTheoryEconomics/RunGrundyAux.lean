import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunBoundary
import AFTD.Kb.GameTheoryEconomics.RunMoveLegal
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# run_grundy_aux

Topic: combinatorial_games   Node: d4a86d0360c9

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:417

The auxiliary Grundy value function for a run of length k with boundary conditions α and β in the Game of Arrows, computed by recursion up to depth bound n using the minimum excluded value of reachable options.
-/

/-- Recursive auxiliary function computing the Grundy value of a run of length k with boundary conditions α and β up to depth bound n. -/
def run_grundy_aux (n : ℕ) (k : ℕ) (α β : RunBoundary) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 =>
    if k = 0 then 0
    else
      let opts : List ℕ :=
        (List.range k).flatMap fun idx =>
          let j := idx + 1
          [RunBoundary.blocked_in, RunBoundary.blocked_out].filterMap fun δ =>
            if run_move_legal k α β j δ then
              some (run_grundy_aux n (j - 1) α δ ^^^ run_grundy_aux n (k - j) δ β)
            else
              none
      nat_mex_list opts
