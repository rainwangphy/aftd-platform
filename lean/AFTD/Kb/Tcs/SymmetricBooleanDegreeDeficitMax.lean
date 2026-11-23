import AFTD.Prelude

/-!
# symmetric_boolean_degree_deficit_max

Topic: algebraic_complexity   Node: ef51c0afc5b9

Provenance: formalization of a published result. Source: arXiv:2611.26446, Sec. 1.1, Eq. (390)

Let $\Delta(n)$ be the maximum degree deficit $n - \deg(q_F)$ over all nonconstant Boolean profiles $F: \{0, \dots, n\} \to \{0, 1\}$, where $q_F \in \mathbb{R}[X]$ is the degree-at-most-$n$ polynomial interpolating $F$.
-/

/-- The maximum degree deficit Δ(n) over all nonconstant Boolean profiles on {0, ..., n}. -/
noncomputable def symmetric_boolean_degree_deficit_max (n : ℕ) : ℕ := Finset.univ.sup (fun F : Fin (n + 1) → Bool =>
    if ∃ i j : Fin (n + 1), F i ≠ F j then
      n - (Lagrange.interpolate Finset.univ (fun (j : Fin (n + 1)) => (j.val : ℝ))
        (fun j => if F j then 1 else 0)).natDegree
    else 0)
