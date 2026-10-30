import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointMultiplicity
import AFTD.Kb.Tcs.WildJointColorType

/-!
# wild_joint_type_weight

Topic: graphs   Node: b8c6055f9dd1

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The total mu-weight sum_T mu(T) * #{i : colour_type(T,i) = X} of triples whose colours have orbit type X relative to that triple. Its four values for X = 0,1,2,3 are the coefficients Q, 3W-Q, 3W-Q, (n-6)W+Q appearing in the identity.
-/

/-- Type weight: sum_T mu(T) * #{i : color_type(T,i) = X}. -/
noncomputable def wild_joint_type_weight (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (X : ℕ) : ℝ := Finset.sum (Finset.univ.filter (fun T : Finset (Fin (3*q)) => T.card = 3)) (fun T => (wild_joint_multiplicity q A T : ℝ) * ((Finset.univ.filter (fun i : Fin (3*q) => wild_joint_color_type q A T i = X)).card : ℝ))
