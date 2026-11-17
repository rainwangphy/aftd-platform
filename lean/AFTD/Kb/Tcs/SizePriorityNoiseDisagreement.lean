import AFTD.Prelude
import AFTD.Kb.Tcs.SizePriorityMatching

/-!
# size_priority_noise_disagreement

Topic: graphs   Node: 51f0bf165a1f

Provenance: original. Related work: OP-1789: the expected normalized symmetric difference between the size-priority optimal matching of the random bipartite graph G(n,n,1-exp(-c/n)) with Uniform[0,1] costs and that after resampling each cost with probability p; building on arXiv:2601.20502.

D_n(c,p) = E[|M Δ M'|]/(2n), written out: the sum over edge sets E ⊆ Fin n × Fin n (each pair present independently with probability 1 - exp(-c/n), so weight (1-exp(-c/n))^|E| · exp(-c/n)^(n·n-|E|)) and over resampling sets R ⊆ Fin n × Fin n (each pair resampled independently with probability p, weight p^|R|·(1-p)^(n·n-|R|)) of the integral, over two independent families ω.1, ω.2 of i.i.d. Uniform[0,1] costs indexed by Fin n × Fin n (the product of the uniform measure on the unit interval), of |M Δ M'|/(2n), where M = size_priority_matching n E ω.1 and M' = size_priority_matching n E w' with w'(e) = ω.2(e) for e ∈ R and ω.1(e) otherwise.
-/

noncomputable def size_priority_noise_disagreement (n : ℕ) (c p : ℝ) : ℝ :=
  ∑ E : Finset (Fin n × Fin n), ∑ R : Finset (Fin n × Fin n),
    (1 - Real.exp (-c / n)) ^ E.card * Real.exp (-c / n) ^ (n * n - E.card) *
    (p ^ R.card * (1 - p) ^ (n * n - R.card)) *
    ∫ ω : (Fin n × Fin n → unitInterval) × (Fin n × Fin n → unitInterval),
      ((symmDiff (size_priority_matching n E (fun e => (ω.1 e : ℝ)))
        (size_priority_matching n E (fun e => if e ∈ R then (ω.2 e : ℝ) else (ω.1 e : ℝ)))).card : ℝ)
        / (2 * n)
