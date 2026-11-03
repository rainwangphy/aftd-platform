import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGapMerge

/-!
# cycle_greedy_moments_all_fuel

Topic: online_algorithms   Node: 473722c81f4b

Provenance: original. Related work: arXiv:2610.15776; OP-891

A recursive function with signature `(fuel : ℕ) → (k_max : ℕ) → (n : ℕ) → (g : List ℕ) → List ℚ`. If `fuel = 0`, it returns the empty list. If `fuel = 1` or `g.length ≤ 1`, letting `m : ℚ := g.head?.getD 0`, it returns the list mapping each `j ∈ [0, k_max]` to `(m / 2)^j / (j + 1)`. For `fuel + 1` with `g.length > 1`, it initializes the accumulator to `1 :: List.replicate k_max 0` and folds over `i ∈ [0, g.length)`, merging gaps at `i` and updating each moment `m ∈ [1, k_max]` by the binomial sum of the immediate cost moments `(l^(j+1) + r^(j+1)) / (2^(j+1) * (j+1) * n)` and subproblem moments `sub.getD (m - j) 0`.
-/

/-- Dynamic programming recurrence computing moments 0 through k_max of greedy cost on cycle gap configuration g with fuel. -/
def cycle_greedy_moments_all_fuel : ℕ → ℕ → ℕ → List ℕ → List ℚ
  | 0, _, _, _ => []
  | 1, k_max, _, g =>
    let m : ℚ := g.head?.getD 0
    (List.range (k_max + 1)).map (fun (j : ℕ) => (m / 2) ^ j / ((j : ℚ) + 1))
  | fuel + 1, k_max, n, g =>
    let k := g.length
    if k ≤ 1 then
      let m : ℚ := g.head?.getD 0
      (List.range (k_max + 1)).map (fun (j : ℕ) => (m / 2) ^ j / ((j : ℚ) + 1))
    else
      let init : List ℚ := 1 :: List.replicate k_max 0
      (List.range k).foldl (fun (acc : List ℚ) (i : ℕ) =>
        let l : ℚ := g[(i + k - 1) % k]?.getD 0
        let r : ℚ := g[i]?.getD 0
        let next_g := cycle_gap_merge g i
        let sub := cycle_greedy_moments_all_fuel fuel k_max n next_g
        (List.range (k_max + 1)).map (fun (m : ℕ) =>
          if m = 0 then 1
          else
            let term : ℚ := (List.range (m + 1)).foldl (fun (t : ℚ) (j : ℕ) =>
              let ex_j : ℚ := (l ^ (j + 1) + r ^ (j + 1)) / (2 ^ (j + 1) * ((j : ℚ) + 1) * (n : ℚ))
              let ey : ℚ := sub.getD (m - j) 0
              t + (Nat.choose m j : ℚ) * ex_j * ey
            ) 0
            acc.getD m 0 + term
        )
      ) init
