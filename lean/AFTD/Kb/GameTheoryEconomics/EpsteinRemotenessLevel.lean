import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EpsteinDown
import AFTD.Kb.GameTheoryEconomics.EpsteinUp

/-!
# epstein_remoteness_level

Topic: combinatorial_games   Node: 3a987228d816

Provenance: formalization of a published result. Source: arXiv:2611.05898 Def 1.2

The set epstein_remoteness_level k of positions with remoteness k in Epstein's put-or-take game: level 0 contains only 0; for odd k = 2m+1, positions n ≠ 0 where at least one move epstein_down n or epstein_up n is in level 2m and neither move is in level 2j for any j < m; for even k = 2m+2, positions n ≠ 0 where both moves belong to the union of odd levels 2j+1 for j ≤ m and at least one move is in level 2m+1.
-/

/-- The set of game positions in Epstein's put-or-take-a-square game having remoteness exactly k. -/
def epstein_remoteness_level : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 =>
    if (k + 1) % 2 = 1 then
      let m := k / 2
      {n : ℕ | n ≠ 0 ∧
        (epstein_down n ∈ epstein_remoteness_level (2 * m) ∨
         epstein_up n ∈ epstein_remoteness_level (2 * m)) ∧
        ∀ j < m, epstein_down n ∉ epstein_remoteness_level (2 * j) ∧
                 epstein_up n ∉ epstein_remoteness_level (2 * j)}
    else
      let m := (k - 1) / 2
      {n : ℕ | n ≠ 0 ∧
        (epstein_down n ∈ (⋃ j ≤ m, epstein_remoteness_level (2 * j + 1))) ∧
        (epstein_up n ∈ (⋃ j ≤ m, epstein_remoteness_level (2 * j + 1))) ∧
        (epstein_down n ∈ epstein_remoteness_level (2 * m + 1) ∨
         epstein_up n ∈ epstein_remoteness_level (2 * m + 1))}
