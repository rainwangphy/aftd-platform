import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_two_rich_colors_no_three_edge_path

Topic: graphs   Node: 04176e1633a8

Provenance: helper lemma. Structural reduction for the eight-vertex cube obstruction; experiments 31165 and 31166.

Under a proper edge coloring, if all rich edges use two colors, no three distinct rich edges can form an adjacent three-edge path.
-/

theorem op309_two_rich_colors_no_three_edge_path
    {V α : Type*} (G : SimpleGraph V) (c : G.lineGraph.Coloring α)
    (a b : α) (e f g : G.edgeSet)
    (hef : G.lineGraph.Adj e f) (hfg : G.lineGraph.Adj f g) (heg : e ≠ g)
    (hre : simple_graph_edge_is_rich G c e)
    (hrf : simple_graph_edge_is_rich G c f)
    (hrg : simple_graph_edge_is_rich G c g)
    (hc : ∀ h : G.edgeSet, simple_graph_edge_is_rich G c h → c h = a ∨ c h = b) :
    False := by
  have h₁ : c e ≠ c f := c.map_rel' hef
  have h₂ : c f ≠ c g := c.map_rel' hfg
  have h₃ : c e ≠ c g := hrf e g (G.lineGraph.adj_symm hef) hfg heg
  rcases hc e hre with he | he <;> rcases hc f hrf with hf | hf <;>
    rcases hc g hrg with hg | hg <;> simp_all
