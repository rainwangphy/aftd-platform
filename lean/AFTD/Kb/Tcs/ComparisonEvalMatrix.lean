import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonPhi2
import AFTD.Kb.Tcs.ComparisonFeature2

/-!
# comparison_eval_matrix

Topic: quantum   Node: 2a9b7e493705

Provenance: formalization of a published result. Source: arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, the notation before Lemma 1

The real evaluation matrix of F_2 on strict orders, with rows indexed by the permutations x of Fin n (strict orders given by ranks) and columns by comparison_feature2 n: its entry at (x, i) is phi_2(x) i. Its kernel is the evaluation kernel of F_2 (coefficient vectors c with <phi_2(x), c> = 0 for every strict order x).
-/

/-- The real evaluation matrix of F_2 on strict orders, with rows indexed by the permutations x of Fin n (strict orders given by ranks) and columns by comparison_feature2 n: its entry at (x, i) is phi_2(x) i. Its kernel is the evaluation kernel of F_2 (coefficient vectors c with <phi_2(x), c> = 0 for every strict order x). -/
def comparison_eval_matrix (n : ℕ) : Matrix (Equiv.Perm (Fin n)) (comparison_feature2 n) ℝ :=
  Matrix.of fun x i => comparison_phi2 x i
