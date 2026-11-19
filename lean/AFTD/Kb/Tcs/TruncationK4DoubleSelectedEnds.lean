import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationK4DoubleSelectedPairs

/-!
# truncation_k4_double_selected_ends

Topic: graphs   Node: 75e50b5939da

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The six unordered edges of the complete graph on four vertices in the specified order.
-/

def truncation_k4_double_selected_ends (e : Fin 6) : Sym2 (Fin 4) :=
  s((truncation_k4_double_selected_pairs e).1, (truncation_k4_double_selected_pairs e).2)
