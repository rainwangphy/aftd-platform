import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointColorType
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointTypeA
import AFTD.Kb.Tcs.WildJointTypeB
import AFTD.Kb.Tcs.WildJointTypeC
import AFTD.Kb.Tcs.WildJointTypeD

/-!
# wild_joint_alpha_of_color_type

Topic: graphs   Node: 309597b75d5e

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The alpha of the type of the pair (T,i): an if-chain on colour_type(T,i) selecting alpha at the concrete triple of that type. Because colour_type always lies in {0,1,2,3}, this is the glue value; summing over i gives sum_X alpha_X * #{i : colour_type(T,i) = X}.
-/

/-- Alpha of the orbit type of (T,i). -/
noncomputable def wild_joint_alpha_of_color_type (q : ℕ) (hq : 3 ≤ q) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (T : Finset (Fin (3*q))) (i : Fin (3*q)) : ℝ := if wild_joint_color_type q A T i = 0 then wild_joint_alpha q (wild_joint_type_A q hq) else if wild_joint_color_type q A T i = 1 then wild_joint_alpha q (wild_joint_type_B q hq) else if wild_joint_color_type q A T i = 2 then wild_joint_alpha q (wild_joint_type_C q hq) else wild_joint_alpha q (wild_joint_type_D q hq)
