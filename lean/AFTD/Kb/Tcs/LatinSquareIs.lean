import AFTD.Prelude

/-!
# latin_square_is

Topic: combinatorics   Node: b93ef6499dfc

Provenance: formalization of a published result. Source: arXiv:2610.20008 (Avoiding a partial Latin square with an isotope of a given Latin square), Sec. 1 (Latin squares as functions [n]² → [n]).

A Latin square of order n: an n × n array with entries in {1, ..., n} whose rows and columns are permutations of {1, ..., n}.
-/

/-- `L` is a Latin square of order `n`: every row `L i` and every column `fun i => L i j` is injective, hence a permutation of `Fin n`. -/
def latin_square_is {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Injective (L i)) ∧ ∀ j, Function.Injective fun i => L i j
