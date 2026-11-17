import AFTD.Prelude
import AFTD.Kb.Tcs.IsSizePriorityOptimal

/-!
# size_priority_matching

Topic: graphs   Node: bd59127f9c2f

Provenance: helper lemma. Defined for OP-1789 (size-priority matching noise phase transition), building on arXiv:2601.20502 (Optimal matching under size priority), Section 1.

A chosen size-priority optimal matching of the bipartite graph on Fin n + Fin n with edge set E under costs w (Hilbert's epsilon of is_size_priority_optimal n E w); one always exists, and it is unique except on the null set of cost vectors with ties.
-/

noncomputable def size_priority_matching (n : ℕ) (E : Finset (Fin n × Fin n))
    (w : Fin n × Fin n → ℝ) : Finset (Fin n × Fin n) :=
  Classical.epsilon (fun M => is_size_priority_optimal n E w M)
