import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGapMerge

/-!
# cycle_greedy_moments_fuel

Topic: online_algorithms   Node: b489574bdd7a

Provenance: formalization of a published result. Source: arXiv:2610.15776, Corollary 18 and Appendix A.2

A function with signature `(fuel : ℕ) → (n : ℕ) → (g : List ℕ) → ℚ × ℚ`. If `fuel = 0`, it returns `(0, 0)`. If `fuel = 1` or `g.length ≤ 1`, letting `m : ℚ := g.head?.getD 0`, it returns terminal cost `(m / 4, m ^ 2 / 12)`. For `fuel + 1` with `fuel ≥ 1` and `g.length > 1`, it computes the fold over `i ∈ [0, g.length)` starting from `(0, 0)` with accumulator update `(acc.1 + c + p * sub1, acc.2 + d + 2 * c * sub1 + p * sub2)`, where `l := g[(i + k - 1) % k]?.getD 0`, `r := g[i]?.getD 0`, `p := (l + r) / (2 * n)`, `c := (l^2 + r^2) / (8 * n)`, `d := (l^3 + r^3) / (24 * n)`, and `(sub1, sub2)` evaluates `cycle_greedy_moments_fuel fuel n (cycle_gap_merge g i)`.
-/

/-- Exact dynamic programming recursion with fuel computing first and second moments of remaining greedy assignment cost from gap state g. -/
def cycle_greedy_moments_fuel : ℕ → ℕ → List ℕ → ℚ × ℚ
  | 0, _, _ => (0, 0)
  | 1, _, g =>
    let m : ℚ := g.head?.getD 0
    (m / 4, m ^ 2 / 12)
  | fuel + 1, n, g =>
    let k := g.length
    if k ≤ 1 then
      let m : ℚ := g.head?.getD 0
      (m / 4, m ^ 2 / 12)
    else
      (List.range k).foldl (fun (acc : ℚ × ℚ) (i : ℕ) =>
        let l : ℚ := g[(i + k - 1) % k]?.getD 0
        let r : ℚ := g[i]?.getD 0
        let next_g := cycle_gap_merge g i
        let (sub1, sub2) := cycle_greedy_moments_fuel fuel n next_g
        let p : ℚ := (l + r) / (2 * n)
        let c : ℚ := (l ^ 2 + r ^ 2) / (8 * n)
        let d : ℚ := (l ^ 3 + r ^ 3) / (24 * n)
        (acc.1 + c + p * sub1,
         acc.2 + d + 2 * c * sub1 + p * sub2)
      ) (0, 0)
