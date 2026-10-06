import AFTD.Prelude

/-!
# mnw2_case3_aux_nonneg_3

Topic: fair_division   Node: 91fc7fdcbc61

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

A specific quartic polynomial with nonnegative coefficients in ten nonnegative variables is nonnegative. It is part 3 of 4 of the slack term of the Positivstellensatz certificate in the hard case of the two-agent price-of-MNW upper bound (split only to keep elaboration fast).
-/

/-- Nonnegativity of part 3 of 4 of an auxiliary quartic used in the certificate for the hard case of the two-agent price-of-MNW bound. -/
theorem mnw2_case3_aux_nonneg_3 (p q r s α β γ δ e3 e4 : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4) : 0 ≤ (96/5)*q*r*s^2 + (211/10)*q*r*s*β + (193/10)*q*r*s*γ + (108/5)*q*r*s*δ + (79271/10)*q*r*α^2 + 18*q*r*β^2 + (107/5)*q*r*β*γ + (88/5)*q*r*β*δ + (41/2)*q*r*γ^2 + (219/10)*q*r*γ*δ + (187/10)*q*r*δ^2 + (104/5)*q*s^3 + (1107/10)*q*s^2*α + (173/10)*q*s^2*β + 21*q*s^2*γ + (86/5)*q*s^2*δ + (51215/2)*q*s*α*γ + (213/10)*q*s*β^2 + (91/5)*q*s*β*γ + (123/5)*q*s*β*δ + (203/10)*q*s*γ^2 + (193/10)*q*s*γ*δ + (209/10)*q*s*δ^2 + (85168/5)*q*α^2*β + 1255*q*α^2*δ + (48049/5)*q*α^2*e4 + (68221/2)*q*α*e4^2 + (213/10)*q*β^3 + (43/2)*q*β^2*γ + (99/5)*q*β^2*δ + (103/5)*q*β*γ^2 + (127/5)*q*β*γ*δ + (203/10)*q*β*δ^2 + (189/10)*q*γ^3 + 17*q*γ^2*δ + (199/10)*q*γ*δ^2 + (197/10)*q*δ^3 + 19*r^4 + (94/5)*r^3*s + (193/10)*r^3*β + (113/5)*r^3*γ + (41/2)*r^3*δ + (98/5)*r^2*s^2 + (92/5)*r^2*s*β + 22*r^2*s*γ + 21*r^2*s*δ + (219/10)*r^2*β^2 + 21*r^2*β*γ + (97/5)*r^2*β*δ + (191/10)*r^2*γ^2 + (106/5)*r^2*γ*δ + (217/10)*r^2*δ^2 + (5097/10)*r*s^3 + (101/5)*r*s^2*β + (196509/10)*r*s^2*γ + (45/2)*r*s^2*δ + (175967/10)*r*s*α*e4 + (203/10)*r*s*β^2 + (207/10)*r*s*β*γ + (97/5)*r*s*β*δ + (96/5)*r*s*γ^2 := by
  positivity
