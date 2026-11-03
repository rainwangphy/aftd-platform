import AFTD.Prelude

/-!
# cycle_greedy_costs

Topic: online_algorithms   Node: b0d0bafe1eae

Provenance: formalization of a published result. Source: arXiv:2610.15776

Given n facilities placed at integers 0, ..., n-1 on the circle ℝ/nℤ and an arrival sequence x in Fin n -> Real arriving in sequential order 0, ..., n-1, cycle_greedy_costs n x is the function mapping each i in Fin n to the shortest-arc distance from arrival x i to its assigned nearest free facility in Fin n, where shortest-arc distance is |(x i - j) - n * round((x i - j)/n)| and ties among equidistant free facilities are broken by choosing the facility with the smallest index j.
-/

/-- Vector of shortest-arc distances paid by each of n successive continuous arrivals on a circle of circumference n under nearest-free greedy facility assignment. -/
noncomputable def cycle_greedy_costs (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  let circ_dist (a : ℝ) (j : Fin n) : ℝ :=
    if n = 0 then 0
    else
      let d := a - (j.val : ℝ)
      let k : ℝ := ((⌊d / (n : ℝ) + 1 / 2⌋ : ℤ) : ℝ)
      |d - (n : ℝ) * k|
  let choose (free : Finset (Fin n)) (h : free.Nonempty) (x : ℝ) : Fin n :=
    let min_d := (free.image (circ_dist x)).min' (Finset.Nonempty.image h _)
    let candidates := free.filter (fun j => circ_dist x j = min_d)
    candidates.min' (by
      have hmem := Finset.min'_mem (free.image (circ_dist x)) (Finset.Nonempty.image h _)
      rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq⟩⟩)
  let step (free : Finset (Fin n)) (x : ℝ) : ℝ × Finset (Fin n) :=
    if h : free.Nonempty then
      let best := choose free h x
      (circ_dist x best, free.erase best)
    else
      (0, free)
  let cost_list := ((List.finRange n).foldl
    (fun (acc : List ℝ × Finset (Fin n)) (i : Fin n) =>
      let (c, free') := step acc.2 (x i)
      (acc.1 ++ [c], free'))
    ([], Finset.univ)).1
  fun i => cost_list.getD i.val 0
