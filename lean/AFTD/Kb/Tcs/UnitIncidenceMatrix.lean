import AFTD.Prelude

/-!
# unit_incidence_matrix

Topic: combinatorics   Node: 51f5425714bd

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

The matrix whose row i is the unit difference e_{u i} − e_{v i} in Z^{n}.
-/

/-- Matrix whose rows are differences of standard basis vectors (the rows of a collision matrix after splitting into two sides). -/
def unit_incidence_matrix {m n : Type*} [DecidableEq n] (u v : m → n) : Matrix m n ℤ := Matrix.of (fun i j => (if u i = j then (1 : ℤ) else 0) - (if v i = j then 1 else 0))
