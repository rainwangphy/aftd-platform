import AFTD.Prelude

/-!
# mnw2_case3_aux_nonneg_2

Topic: fair_division   Node: 3ac4988e7234

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

A specific quartic polynomial with nonnegative coefficients in ten nonnegative variables is nonnegative. It is part 2 of 4 of the slack term of the Positivstellensatz certificate in the hard case of the two-agent price-of-MNW upper bound (split only to keep elaboration fast).
-/

/-- Nonnegativity of part 2 of 4 of an auxiliary quartic used in the certificate for the hard case of the two-agent price-of-MNW bound. -/
theorem mnw2_case3_aux_nonneg_2 (p q r s α β γ δ e3 e4 : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4) : 0 ≤ (106/5)*p*r*β^2 + (104/5)*p*r*β*γ + (177/10)*p*r*β*δ + (106/5)*p*r*γ^2 + (237/10)*p*r*γ*δ + (97/5)*p*r*δ^2 + (201/10)*p*s^3 + 18*p*s^2*β + 22*p*s^2*γ + (99/5)*p*s^2*δ + (1107/5)*p*s*α^2 + (9242/5)*p*s*α*e4 + (109/5)*p*s*β^2 + (103/5)*p*s*β*γ + (227/10)*p*s*β*δ + 2337*p*s*γ^2 + (171/10)*p*s*γ*δ + 20*p*s*δ^2 + 2561*p*s*e4^2 + (16837/10)*p*α*δ*e3 + (43/2)*p*β^3 + (191/10)*p*β^2*γ + (187/10)*p*β^2*δ + (207/10)*p*β*γ^2 + (10537/10)*p*β*γ*δ + (39/2)*p*β*δ^2 + (91/5)*p*γ^3 + (79/5)*p*γ^2*δ + (197/10)*p*γ*δ^2 + (199/10)*p*δ^3 + (163543/10)*p*δ*e3*e4 + (181/10)*q^4 + (104/5)*q^3*r + (199/10)*q^3*s + (4358/5)*q^3*α + (207/10)*q^3*β + (98/5)*q^3*γ + (209/10)*q^3*δ + (107/5)*q^2*r^2 + (209/10)*q^2*r*s + (61607/10)*q^2*r*α + 22*q^2*r*β + (183/10)*q^2*r*γ + (209/10)*q^2*r*δ + 22*q^2*s^2 + 18*q^2*s*β + (99/5)*q^2*s*γ + (33/2)*q^2*s*δ + (84322/5)*q^2*α^2 + (95783/10)*q^2*α*δ + (45731/5)*q^2*α*e4 + (101/5)*q^2*β^2 + (171/10)*q^2*β*γ + (106/5)*q^2*β*δ + (207/10)*q^2*γ^2 + (187/10)*q^2*γ*δ + (191/10)*q^2*δ^2 + (207/10)*q*r^3 + (107/5)*q*r^2*s + (91/5)*q*r^2*β + (183/10)*q*r^2*γ + (183/10)*q*r^2*δ := by
  positivity
