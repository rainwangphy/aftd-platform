import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonEdge

/-!
# comparison_sign

Topic: quantum   Node: 5abac3938f19

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real-valued comparison sign d_e(x) of a strict order. A strict order on the labels Fin n is given by a permutation x : Equiv.Perm (Fin n), x i being the rank of label i. For an edge e = (a, b) with a < b, comparison_sign x e is the real number 1 if x a < x b and the real number -1 otherwise.
-/

/-- The real-valued comparison sign d_e(x) of a strict order. A strict order on the labels Fin n is given by a permutation x : Equiv.Perm (Fin n), x i being the rank of label i. For an edge e = (a, b) with a < b, comparison_sign x e is the real number 1 if x a < x b and the real number -1 otherwise. -/
def comparison_sign {n : ℕ} (x : Equiv.Perm (Fin n)) (e : comparison_edge n) : ℝ :=
  if x e.1.1 < x e.1.2 then 1 else -1
