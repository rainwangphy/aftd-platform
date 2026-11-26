import AFTD.Prelude
import AFTD.Kb.Tcs.Op874QuotientMonoRel
import AFTD.Kb.Tcs.Op874QuotientMonoDegree

/-!
# op874_quotient_saturated_component

Topic: graphs   Node: 83defe60c624

Provenance: helper lemma. Maximum-cut and low-port structural reduction for OP-874, https://arxiv.org/abs/2610.41950; related degree-four cut structure: https://www.math.ru.nl/OpenGraphProblems/Gerjan/Kostochka5.pdf.

The same-side connected component of x consists entirely of vertices with same-side degree two.
-/

def op874_quotient_saturated_component {X E : Type*} [DecidableEq X] [Fintype E] (l r : E → X) (b : X → Bool) (x : X) : Prop := ∀ y, Relation.ReflTransGen (op874_quotient_mono_rel l r b) x y → op874_quotient_mono_degree l r b y = 2
