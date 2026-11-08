import AFTD.Prelude

/-!
# latin_block_weight

Topic: matching_markets   Node: 1acf46bb7a8f

Provenance: helper lemma. step towards opposed_latin_blocking_variance_div_cube_tendsto

For the opposed Latin market of L and two men i, k (i ≠ k), the weight of the ordered pair (i,k) at values a = L(i, μ i) and b = L(i, μ k): it is 1 when man i strictly prefers the woman matched to man k over his own partner (b < a, since a smaller L-value is a better position for a man) and that woman strictly prefers man i to man k (c = L(k, μ k) < b, since a woman's position for a man is n − L and smaller is better).
-/

/-- Indicator of the ordered pair of men (i,k), evaluated at a = L i (μ i) and b = L i (μ k): 1 exactly when man i prefers the woman matched to man k and she prefers man i to man k. -/
def latin_block_weight {n : ℕ} (L : Fin n → Fin n → Fin n) (i k : Fin n) (a b : Fin n) : ℕ := if L i b < L i a ∧ L k b < L i b then 1 else 0
