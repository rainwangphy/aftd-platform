import AFTD.Prelude

/-!
# cubicHypergraphCocycle

Topic: quantum   Node: 51be4e7e00dd

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

For a hypergraph H on n vertices (a finite set of finite sets of Fin n) and a bit string x : Fin n → Fin 2, the real ±1 cocycle χ_H(x) = ∏_{e ∈ H} (−1)^{[∀ i ∈ e, x i = 1]}.
-/

/-- Real ±1 hypergraph cocycle; each coordinate of `hypergraphState` is (2^n)^{-1/2} times χ_H(x). -/
noncomputable def cubicHypergraphCocycle (n : ℕ) (H : Finset (Finset (Fin n))) (x : Fin n → Fin 2) : ℝ := ∏ e ∈ H, if ∀ i ∈ e, x i = 1 then (-1 : ℝ) else 1
