import AFTD.Prelude

/-!
# op1525_colsupp

Topic: combinatorics   Node: 054b8889bc11

Provenance: helper lemma. step towards op1525_diagonal_symmetric_deletion_reconstruct

The set of rows occupied in column c by the subset S of the t×m array: the row set of the cells of S lying in column c.
-/

/-- Column support: the rows occupied by S in column c. -/
def op1525_colsupp {t m : ℕ} (S : Finset (Fin t × Fin m)) (c : Fin m) : Finset (Fin t) := (S.filter (fun x => x.2 = c)).image (fun x => x.1)
