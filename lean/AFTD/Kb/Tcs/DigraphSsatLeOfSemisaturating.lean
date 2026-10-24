import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSsat
import AFTD.Kb.Tcs.DigraphIsSemisaturating
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_ssat_le_of_semisaturating

Topic: graphs   Node: 9fd3d3972102

Provenance: helper lemma. arXiv:2610.18600 Definition 1.2

If H : Digraph (Fin n) is a host digraph on Fin n with DecidableRel H.Adj such that digraph_is_semisaturating H G holds, then digraph_ssat n G ≤ digraph_edge_count H.
-/

/-- Any host digraph semisaturating G gives an upper bound on digraph_ssat. -/
theorem digraph_ssat_le_of_semisaturating {V : Type*} (n : ℕ) (G : Digraph V) (H : Digraph (Fin n)) [d : DecidableRel H.Adj] (hH : digraph_is_semisaturating H G) : digraph_ssat n G ≤ digraph_edge_count H := by
  unfold digraph_ssat
  exact Nat.sInf_le ⟨H, d, hH, rfl⟩
