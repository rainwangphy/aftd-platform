import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_nullity_poly

Topic: combinatorics   Node: d41d933ebefb

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

The nullity generating polynomial of a finite graph G on V: the sum over all vertex subsets F of w raised to the nullity of the partial Petrial matrix at F, i.e. w^(|V| - rank (petrial_matrix G F)). Equivalently, the coefficient of w^j is the number of F : Finset V for which petrial_matrix G F has nullity j.
-/

/-- The nullity generating polynomial of a finite graph: the coefficient of w^j counts the subsets F whose partial Petrial matrix has nullity j. -/
noncomputable def petrial_nullity_poly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Polynomial ℕ := ∑ F : Finset V, Polynomial.X ^ (Fintype.card V - (petrial_matrix G F).rank)
