import AFTD.Prelude

/-!
# swing_table

Topic: general_equilibrium   Node: d06ea308b97a

Provenance: formalization of a published result. Source: What Semivalues Cannot See: The Information Content of Anonymous Marginal Values, arXiv:2607.07013, Sec. 10 (simple game, weighted game as in the monograph Simple Games: Desirability Relations, Trading, Pseudoweightings (1999), swing table)

The swing table of a game: T(i, k) is the number of coalitions S of size k not containing i such that S together with i wins while S loses.
-/

/-- The swing table of a game (arXiv:2607.07013, Sec. 10): `T i k` counts the coalitions `S` of size `k` not containing `i` for which `i` is a swing, i.e. `S ∪ {i}` wins and `S` loses. -/
def swing_table {n : ℕ} (v : Finset (Fin n) → Bool) (i : Fin n) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n) =>
    i ∉ S ∧ S.card = k ∧ v (insert i S) = true ∧ v S = false).card
