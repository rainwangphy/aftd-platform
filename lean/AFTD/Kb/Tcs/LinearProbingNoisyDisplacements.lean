import AFTD.Prelude
import AFTD.Kb.Tcs.LinearProbingDisplacements

/-!
# linear_probing_noisy_displacements

Topic: online_algorithms   Node: e5dfe5da0faf

Provenance: formalization of a published result. Source: knowledgebase, OP-894

Given $n \ge 1$, home slot assignments $h : \text{Fin } n \to \mathbb{Z}/n\mathbb{Z}$, and a noise vector $\xi : \text{Fin } n \to \mathbb{R}$, the noisy displacement vector assigns to each key $i \in \text{Fin } n$ the sum of its linear probing displacement under $h$ and the noise coordinate $\xi(i)$.
-/

/-- The displacement vector of linear probing plus continuous uniform noise. -/
noncomputable def linear_probing_noisy_displacements (n : ℕ) [NeZero n]
    (p : (Fin n → ZMod n) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => (linear_probing_displacements n p.1 i : ℝ) + p.2 i
