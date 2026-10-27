import AFTD.Prelude

/-!
# dominating_average_stability_path_five_decidable

Topic: graphs   Node: f2098241898b

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

An explicit computable adjacency decision for the five-vertex path.
-/

def dominating_average_stability_path_five_decidable :
    DecidableRel (SimpleGraph.pathGraph 5).Adj :=
  fun u v => decidable_of_iff (u.val+1=v.val ∨ v.val+1=u.val)
    SimpleGraph.pathGraph_adj.symm
