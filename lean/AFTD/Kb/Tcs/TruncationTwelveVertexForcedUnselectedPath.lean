import AFTD.Prelude
import AFTD.Kb.Tcs.RequiredEdgesExhaustLowPorts
import AFTD.Kb.Tcs.TruncationTwelveVertexRequiredEdges

/-!
# truncation_twelve_vertex_forced_unselected_path

Topic: graphs   Node: ec66ecc83fa2

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

If twelve chosen ports cover the twelve listed required edges, each of the four edges of the path 6,7,8,9,10 is unselected at both ends.
-/

theorem truncation_twelve_vertex_forced_unselected_path
    (low : Fin 12 → Fin 12)
    (hcover : ∀ e ∈ truncation_twelve_vertex_required_edges, ∃ v, s(v, low v) = e) :
    low 6 ≠ 7 ∧ low 7 ≠ 6 ∧ low 7 ≠ 8 ∧ low 8 ≠ 7 ∧
      low 8 ≠ 9 ∧ low 9 ≠ 8 ∧ low 9 ≠ 10 ∧ low 10 ≠ 9 := by
  have hc : truncation_twelve_vertex_required_edges.card = Fintype.card (Fin 12) := by decide
  have hsel := required_edges_exhaust_low_ports truncation_twelve_vertex_required_edges low hc hcover
  have hnot : ∀ u v : Fin 12, s(u, v) ∉ truncation_twelve_vertex_required_edges → low u ≠ v := by
    intro u v hnone h
    have he := hsel u
    rw [h] at he
    exact hnone he
  refine ⟨hnot 6 7 (by decide), hnot 7 6 (by decide),
    hnot 7 8 (by decide), hnot 8 7 (by decide),
    hnot 8 9 (by decide), hnot 9 8 (by decide),
    hnot 9 10 (by decide), hnot 10 9 (by decide)⟩
