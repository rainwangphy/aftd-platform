import AFTD.Prelude

/-!
# mnw2_case3_aux_nonneg_1

Topic: fair_division   Node: c0e83f66d8f3

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

A specific quartic polynomial with nonnegative coefficients in ten nonnegative variables is nonnegative. It is part 1 of 4 of the slack term of the Positivstellensatz certificate in the hard case of the two-agent price-of-MNW upper bound (split only to keep elaboration fast).
-/

/-- Nonnegativity of part 1 of 4 of an auxiliary quartic used in the certificate for the hard case of the two-agent price-of-MNW bound. -/
theorem mnw2_case3_aux_nonneg_1 (p q r s α β γ δ e3 e4 : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4) : 0 ≤ (199/10)*p^4 + (38669/5)*p^3*q + (103/5)*p^3*r + (61429/10)*p^3*s + (102/5)*p^3*β + (98/5)*p^3*γ + 20*p^3*δ + (37/2)*p^2*q^2 + (104/5)*p^2*q*r + (217/10)*p^2*q*s + (191/10)*p^2*q*β + (229/10)*p^2*q*γ + (43/2)*p^2*q*δ + (99/5)*p^2*r^2 + (36007/10)*p^2*r*s + 21*p^2*r*β + (87/5)*p^2*r*γ + (39/2)*p^2*r*δ + (203/10)*p^2*s^2 + (37/2)*p^2*s*β + (104/5)*p^2*s*γ + (98/5)*p^2*s*δ + (211/10)*p^2*β^2 + (31/2)*p^2*β*γ + (193/10)*p^2*β*δ + (47/2)*p^2*γ^2 + (20729/5)*p^2*γ*δ + (203/10)*p^2*δ^2 + 6808*p*q^3 + (93/5)*p*q^2*r + (133451/10)*p*q^2*s + (97/5)*p*q^2*β + (113/5)*p*q^2*γ + (107/5)*p*q^2*δ + (113/5)*p*q*r^2 + (181/10)*p*q*r*s + (114/5)*p*q*r*β + (74/5)*p*q*r*γ + (99913/10)*p*q*r*δ + (112/5)*p*q*s^2 + (31/2)*p*q*s*β + (56291/10)*p*q*s*γ + (83/5)*p*q*s*δ + (273071/10)*p*q*α*e4 + (97/5)*p*q*β^2 + (76/5)*p*q*β*γ + (211/10)*p*q*β*δ + (219/10)*p*q*γ^2 + (35/2)*p*q*γ*δ + 20*p*q*δ^2 + (61323/10)*p*q*e4^2 + (197/10)*p*r^3 + (207/10)*p*r^2*s + (193/10)*p*r^2*β + (203/10)*p*r^2*γ + (96/5)*p*r^2*δ + (32892/5)*p*r*s^2 + (40371/5)*p*r*s*β + (29749/5)*p*r*s*γ + (111/5)*p*r*s*δ + (55327/5)*p*r*s*e4 := by
  positivity
