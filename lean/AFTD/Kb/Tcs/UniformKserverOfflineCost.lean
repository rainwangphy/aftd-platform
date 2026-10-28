import AFTD.Prelude

/-!
# uniform_kserver_offline_cost

Topic: online_algorithms   Node: fc83f005e85a

Provenance: formalization of a published result. Source: scout/2610-37192-tight-bounds-for-randomized-generalized-k-server-on-uniform.md:341

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, an initial configuration a, and a list of configurations sched, the offline movement cost is 0 for the empty list and the sum of Hamming distances between consecutive configurations along sched starting from a.
-/

/-- Total movement cost of an offline schedule starting from configuration a. -/
def uniform_kserver_offline_cost {k : ℕ} {M : Fin k → Type*} [∀ i, DecidableEq (M i)] (a : ∀ i, M i) : List (∀ i, M i) → ℕ
  | [] => 0
  | x :: xs => (Finset.univ.filter (fun i => a i ≠ x i)).card + uniform_kserver_offline_cost x xs
