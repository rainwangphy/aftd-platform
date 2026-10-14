import AFTD.Prelude

/-!
# nat_least_prime_not_dvd

Topic: elementary_number_theory   Node: ddf9f277a940

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 2 (q(m)).

q(m): the smallest prime number not dividing m (0 by convention for m = 0, which no prime fails to divide).
-/

/-- `q(m)`: the smallest prime not dividing `m`. -/
noncomputable def nat_least_prime_not_dvd (m : ℕ) : ℕ :=
  sInf {p | p.Prime ∧ ¬ p ∣ m}
