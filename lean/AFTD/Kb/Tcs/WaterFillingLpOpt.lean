import AFTD.Prelude
import AFTD.Kb.Tcs.KthLargest

/-!
# water_filling_lp_opt

Topic: approximation   Node: 0fd6ca84957b

Provenance: formalization of a published result. Source: arXiv:2611.30731 Sec. 2

The optimal value of the water-filling linear programming relaxation for scheduling $n$ jobs with processing times $p$ and weights $w$ on $m$ identical machines, minimizing $\sum_{j} w_j C_j$ subject to $\sum_{j \in S} p_j C_j \ge \frac{1}{2} \sum_{j \in S} p_j^2 + \frac{1}{2} g(p_S)$ for all $S \subseteq \mathrm{Fin}\,n$, where $g(p_S)$ is the infimum of $\sum_{i \in \mathrm{Fin}\,m} L_i^2$ over machine load vectors $L : \mathrm{Fin}\,m \to \mathbb{R}$ with $\sum_{i} L_i = \sum_{j \in S} p_j$ and $L_i \ge \mathrm{kth\_largest}(p_S, i)$.
-/

/-- The optimal objective value of the water-filling LP relaxation for identical parallel machines. -/
noncomputable def water_filling_lp_opt (m n : ℕ) (p w : Fin n → ℝ) : ℝ := sInf { cost : ℝ | ∃ C : Fin n → ℝ,
    (∀ S : Finset (Fin n),
      (1 / 2 : ℝ) * (∑ j ∈ S, (p j) ^ 2) +
      (1 / 2 : ℝ) * sInf { s : ℝ | ∃ L : Fin m → ℝ,
        (∑ i : Fin m, L i = ∑ j ∈ S, p j) ∧
        (∀ i : Fin m, kth_largest (fun j => if j ∈ S then p j else 0) i.1 ≤ L i) ∧
        s = ∑ i : Fin m, (L i) ^ 2 } ≤
      ∑ j ∈ S, p j * C j) ∧
    cost = ∑ j : Fin n, w j * C j }
