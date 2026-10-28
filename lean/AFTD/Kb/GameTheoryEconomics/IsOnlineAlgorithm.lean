import AFTD.Prelude

/-!
# is_online_algorithm

Topic: fair_division   Node: f71077bb96f9

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 2

For an allocation algorithm alg taking a number of goods m : ℕ, predicted valuation profiles a_hat : Fin n → Fin m → ℝ, and true valuation profiles v : Fin n → Fin m → ℝ to an allocation Fin m → Fin n, alg is online if for all m, a_hat, v, v', and step t : Fin m, whenever v and v' agree on all agents and all steps s ≤ t, alg m a_hat v t equals alg m a_hat v' t.
-/

/-- An allocation algorithm is online if the decision at step t depends only on predictions and arrivals up to step t. -/
def is_online_algorithm (n : ℕ) (alg : ∀ m : ℕ, (Fin n → Fin m → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n)) : Prop :=
  ∀ (m : ℕ) (a_hat : Fin n → Fin m → ℝ) (v v' : Fin n → Fin m → ℝ) (t : Fin m),
    (∀ (s : Fin m), s ≤ t → ∀ i : Fin n, v i s = v' i s) → alg m a_hat v t = alg m a_hat v' t
