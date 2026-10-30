import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointInvalidCount
import AFTD.Kb.Tcs.WildJointBadColorCount

/-!
# wild_joint_expected_ID

Topic: graphs   Node: b8299deac37e

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

E[I*D]: the expectation of I(σ)*D(σ) over the uniform distribution on all vertex permutations σ of Fin (3q), i.e. (1/n!) * sum over σ of I*D.
-/

/-- E[I*D] under the uniform distribution on vertex permutations. -/
noncomputable def wild_joint_expected_ID (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) : ℝ := (1 / ((Nat.factorial (3*q) : ℕ) : ℝ)) * (Finset.univ.sum (fun σ : Equiv.Perm (Fin (3*q)) => (wild_joint_invalid_count q A σ : ℝ) * (wild_joint_bad_color_count q A σ : ℝ)))
