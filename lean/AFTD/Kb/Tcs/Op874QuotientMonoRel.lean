import AFTD.Prelude

/-!
# op874_quotient_mono_rel

Topic: graphs   Node: c948f13c87da

Provenance: helper lemma. Maximum-cut and low-port structural reduction for OP-874, https://arxiv.org/abs/2610.41950; related degree-four cut structure: https://www.math.ru.nl/OpenGraphProblems/Gerjan/Kostochka5.pdf.

Adjacency within one side of a cut of an edge-indexed multigraph.
-/

def op874_quotient_mono_rel {X E : Type*} (l r : E → X) (b : X → Bool) (u v : X) : Prop := b u = b v ∧ ∃ e, (l e = u ∧ r e = v) ∨ (l e = v ∧ r e = u)
