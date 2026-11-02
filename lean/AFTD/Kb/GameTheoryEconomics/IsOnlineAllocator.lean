import AFTD.Prelude

/-!
# is_online_allocator

Topic: fair_division   Node: a9ce2771b74f

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 2

An allocation algorithm on m goods for n agents is online if the allocation of each arriving good t depends only on the valuation vectors of goods up to step t.
-/

/-- An allocation algorithm on m goods for n agents is online if the allocation of each arriving good t depends only on the valuation vectors of goods up to step t. -/
def is_online_allocator (n m : ℕ) (alg : (Fin n → Fin m → ℝ) → (Fin m → Fin n)) : Prop := ∀ (v v' : Fin n → Fin m → ℝ) (t : Fin m),
    (∀ (s : Fin m), s ≤ t → ∀ i : Fin n, v i s = v' i s) → alg v t = alg v' t
