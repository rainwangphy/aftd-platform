import AFTD.Prelude

/-!
# identical_parallel_machines_opt

Topic: approximation   Node: 016a574dc46c

Provenance: formalization of a published result. Source: arXiv:2611.30731 Sec. 1

The optimal total weighted completion time of scheduling $n$ jobs with processing times $p$ and weights $w$ on $m$ identical parallel machines, defined as the infimum of $\sum_{j} w_j (S_j + p_j)$ over non-negative start times $S$ and machine assignments $M : \mathrm{Fin}\,n \to \mathrm{Fin}\,m$ such that jobs assigned to the same machine do not overlap.
-/

/-- The optimal offline schedule cost for identical parallel machine scheduling with weighted completion time. -/
noncomputable def identical_parallel_machines_opt (m n : ℕ) (p w : Fin n → ℝ) : ℝ := sInf { cost : ℝ | ∃ (M : Fin n → Fin m) (S : Fin n → ℝ),
    (∀ j, 0 ≤ S j) ∧
    (∀ j k, j ≠ k → M j = M k → S j + p j ≤ S k ∨ S k + p k ≤ S j) ∧
    cost = ∑ j : Fin n, w j * (S j + p j) }
