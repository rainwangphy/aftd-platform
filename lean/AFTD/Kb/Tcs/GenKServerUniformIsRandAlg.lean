import AFTD.Prelude

/-!
# gen_k_server_uniform_is_rand_alg

Topic: online_algorithms   Node: 8a7d5c66d8c1

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2 (Preliminaries): randomized online algorithm for generalized k-server; here every space is the uniform metric Fin m and the algorithm is given in behavioural form by transition probabilities

Generalized k-server where each of the k servers moves in its own copy of the uniform metric on m points: configurations and requests are functions Fin k → Fin m. A real function P(past, r, x, y), taking a list `past` of earlier requests, the current request r, the current configuration x and a next configuration y, is a randomized online algorithm (in behavioural form) if for every past, r and x: P(past, r, x, y) ≥ 0 for every y, the sum over all y in Fin k → Fin m of P(past, r, x, y) is 1, and every y with P(past, r, x, y) ≠ 0 serves r, i.e. y i = r i for some i : Fin k. P(past, r, x, y) is the probability of moving from x to y when request r arrives after the requests `past`.
-/

/-- Randomized online algorithm for generalized k-server on k uniform metrics `Fin m`, given by transition probabilities `P past r x y` (earlier requests, current request, current configuration, next configuration); the next configuration must serve the request. -/
def gen_k_server_uniform_is_rand_alg {k m : ℕ}
    (P : List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ) : Prop :=
  ∀ (past : List (Fin k → Fin m)) (r x : Fin k → Fin m),
    (∀ y, 0 ≤ P past r x y) ∧ (∑ y, P past r x y) = 1 ∧ (∀ y, P past r x y ≠ 0 → ∃ i, y i = r i)
