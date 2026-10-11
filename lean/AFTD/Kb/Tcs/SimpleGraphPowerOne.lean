import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# simple_graph_power_one

Topic: graphs   Node: d640c17e9655

Provenance: helper lemma. Sanity lemma for simple_graph_power (arXiv:2610.09300 (On graphs whose powers are well-covered)).

G^1 = G.
-/

theorem simple_graph_power_one {V : Type*} (G : SimpleGraph V) :
    simple_graph_power G 1 = G := by
  ext u v
  simp only [simple_graph_power]
  constructor
  · rintro ⟨hne, hle⟩
    have h0 : G.edist u v ≠ 0 := by
      intro h; exact hne (SimpleGraph.edist_eq_zero_iff.1 h)
    have h1 : G.edist u v = 1 := by
      have : G.edist u v ≤ 1 := by exact_mod_cast hle
      exact le_antisymm this (Order.one_le_iff_ne_zero.2 h0)
    exact SimpleGraph.edist_eq_one_iff_adj.1 h1
  · intro h
    exact ⟨h.ne, by rw [SimpleGraph.edist_eq_one_iff_adj.2 h]; simp⟩
