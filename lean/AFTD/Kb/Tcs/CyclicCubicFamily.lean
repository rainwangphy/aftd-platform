import AFTD.Prelude

/-!
# cyclic_cubic_family

Topic: quantum   Node: 028b588afd4e

Provenance: helper lemma. step towards cyclic_cubic_t_count_upper_bound

The explicit parametric parity family on n qubits consists of 10 boundary parities (Group A), 2(n-4) running parities (Group B), and 3 span parities (Group C), mapped into Finset (Fin n).
-/

/-- The explicit parametric parity representation family of size 2n + 5 for the cyclic cubic syndrome on n qubits. -/
def cyclic_cubic_family (n : ℕ) : Finset (Finset (Fin n)) :=
  let gA : Finset (Finset ℕ) := {
    {1}, {0, 1},
    {n - 3}, {0, n - 2}, {n - 3, n - 2},
    {1, n - 1}, {0, 1, n - 1},
    {n - 4, n - 1}, {n - 4, n - 3, n - 1},
    {0, n - 2, n - 1}
  }
  let gB : Finset (Finset ℕ) :=
    (Finset.Iic (n - 5)).biUnion (fun k =>
      let tail := Finset.Ico (k + 3) n
      {insert k tail, insert k (insert (k + 1) tail)})
  let gC : Finset (Finset ℕ) := {
    Finset.Ico 2 n,
    insert 0 (Finset.Ico 2 n),
    Finset.Iio n
  }
  let toFin (s : Finset ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ s)
  (gA ∪ gB ∪ gC).image toFin
