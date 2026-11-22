import AFTD.Prelude

/-!
# thermomajorization_witness_triples

Topic: quantum_mechanics   Node: b81d3e40c35c

Provenance: helper lemma. step towards thermomajorization_random_single_probe_sharp_witness_family

For dimension n, thermomajorization_witness_triples n is the finite set of integer triples (a,j,b) in {0,...,n}³ satisfying a < j, j < b and b ≤ n.
-/

/-- The finite set of admissible witness parameters (a,j,b) with a<j<b≤n, used to index the candidate witness family. -/
def thermomajorization_witness_triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 ≤ n)
