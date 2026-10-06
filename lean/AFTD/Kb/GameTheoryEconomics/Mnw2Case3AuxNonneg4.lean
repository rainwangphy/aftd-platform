import AFTD.Prelude

/-!
# mnw2_case3_aux_nonneg_4

Topic: fair_division   Node: 3952c6265785

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

A specific quartic polynomial with nonnegative coefficients in ten nonnegative variables is nonnegative. It is part 4 of 4 of the slack term of the Positivstellensatz certificate in the hard case of the two-agent price-of-MNW upper bound (split only to keep elaboration fast).
-/

/-- Nonnegativity of part 4 of 4 of an auxiliary quartic used in the certificate for the hard case of the two-agent price-of-MNW bound. -/
theorem mnw2_case3_aux_nonneg_4 (p q r s α β γ δ e3 e4 : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4) : 0 ≤ (84/5)*r*s*γ*δ + (94/5)*r*s*δ^2 + (209/10)*r*β^3 + (171/10)*r*β^2*γ + (89/5)*r*β^2*δ + (203/10)*r*β*γ^2 + (109/5)*r*β*γ*δ + (227/10)*r*β*δ^2 + (193/10)*r*γ^3 + (181/10)*r*γ^2*δ + (167/10)*r*γ*δ^2 + (199/10)*r*δ^3 + (193/10)*s^3*β + (104/5)*s^3*γ + (201/10)*s^3*δ + (209/10)*s^2*β^2 + (99/5)*s^2*β*γ + (45/2)*s^2*β*δ + (188403/10)*s^2*γ^2 + (54041/5)*s^2*γ*δ + (98/5)*s^2*δ^2 + (3757/5)*s*α^2*e4 + (56359/10)*s*α*β^2 + (88801/10)*s*α*β*e3 + (17647/10)*s*α*δ^2 + (102/5)*s*β^3 + (97/5)*s*β^2*γ + (183/10)*s*β^2*δ + (109878/5)*s*β*γ^2 + 20*s*β*γ*δ + (96/5)*s*β*δ^2 + (28377/5)*s*γ^3 + (231259/5)*s*γ^2*δ + (131924/5)*s*γ*δ^2 + (174111/5)*s*γ*e3^2 + (201/10)*s*δ^3 + (8621/10)*α^3*e3 + (2353/5)*α^2*β^2 + (64571/10)*α^2*β*δ + 15999*α*β*δ*e3 + 1225*α*γ^2*δ + (34193/10)*α*γ*δ*e3 + (79957/10)*α*δ^3 + (2968/5)*α*δ*e3*e4 + (193/10)*β^4 + (197/10)*β^3*γ + (187/10)*β^3*δ + (41/2)*β^2*γ^2 + (41/2)*β^2*γ*δ + (207/10)*β^2*δ^2 + (209/10)*β*γ^3 + (43/2)*β*γ^2*δ + (37/2)*β*γ*δ^2 + (101/5)*β*δ^3 + (99/5)*γ^4 + (197/10)*γ^3*δ + (211/10)*γ^2*δ^2 + (94221/10)*γ*δ^3 + (56673/5)*γ*δ*e3^2 + 20*δ^4 + 5651*e3^4 + 6108*e4^4 := by
  positivity
