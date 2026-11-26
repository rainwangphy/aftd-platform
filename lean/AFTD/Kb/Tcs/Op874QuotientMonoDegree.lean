import AFTD.Prelude

/-!
# op874_quotient_mono_degree

Topic: graphs   Node: 8d82f8169d3c

Provenance: helper lemma. Maximum-cut and low-port structural reduction for OP-874, https://arxiv.org/abs/2610.41950; related degree-four cut structure: https://www.math.ru.nl/OpenGraphProblems/Gerjan/Kostochka5.pdf.

Number of same-side edges incident to a vertex of an edge-indexed multigraph, counting parallel edges.
-/

def op874_quotient_mono_degree {X E : Type*} [DecidableEq X] [Fintype E] (l r : E → X) (b : X → Bool) (x : X) : ℕ := ((Finset.univ : Finset E).filter fun e => (l e = x ∨ r e = x) ∧ b (l e) = b (r e)).card
