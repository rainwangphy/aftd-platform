import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# simple_graph_achromatic_number

Topic: graphs   Node: 8cedd8c10e48

Provenance: formalization of a published result. Source: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs), Sec. 1, definition of χ_a

χ_a(G) is the maximum number of colours in an achromatic colouring of G.
-/

/-- The achromatic number χ_a(G): the largest number of colours in an achromatic colouring. -/
noncomputable def simple_graph_achromatic_number {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ C : G.Coloring (Fin k), simple_graph_coloring_is_achromatic C}
