import AFTD.Prelude

/-!
# order_prefix

Topic: general_equilibrium   Node: 9bd303b3086a

Provenance: original. Related work: arXiv:2611.16207, Section 3

Given a finite type α with decidable equality, an ordering bijection e : Fin (Fintype.card α) ≃ α, and a natural number k, order_prefix e k is the finite set of elements e(j) for all indices j : Fin (Fintype.card α) strictly less than k.
-/

/-- The prefix of the first k elements of a finite type α under an ordering bijection e : Fin (Fintype.card α) ≃ α. -/
def order_prefix {α : Type*} [DecidableEq α] [Fintype α]
    (e : Fin (Fintype.card α) ≃ α) (k : ℕ) : Finset α := (Finset.univ.filter (fun (j : Fin (Fintype.card α)) => (j : ℕ) < k)).image e
