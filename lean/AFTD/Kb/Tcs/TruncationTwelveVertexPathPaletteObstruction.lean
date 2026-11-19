import AFTD.Prelude
import AFTD.Kb.Tcs.SixCycleThreePathFourColorWindowsObstruction
import AFTD.Kb.Tcs.TruncationTwelveVertexForcedUnselectedPath
import AFTD.Kb.Tcs.TruncationTwelveVertexRequiredEdges

/-!
# truncation_twelve_vertex_path_palette_obstruction

Topic: graphs   Node: f5b11b1813a7

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

For the twelve explicitly listed required edges, a port cover, the stated pair-separation conditions and both three-edge path window conditions cannot hold simultaneously.
-/

theorem truncation_twelve_vertex_path_palette_obstruction
    (low : Fin 12 → Fin 12) (a b c d e f : Fin 4)
    (hcover : ∀ edge ∈ truncation_twelve_vertex_required_edges, ∃ v, s(v, low v) = edge)
    (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a)
    (hmono1 : ({d, e} : Finset (Fin 4)) ≠ {e, f})
    (hmono2 : ({e, f} : Finset (Fin 4)) ≠ {f, a})
    (hmatch : ({b, c} : Finset (Fin 4)) ≠ {e, f})
    (hleft : (low 6 ≠ 7 ∧ low 7 ≠ 6 ∧ low 7 ≠ 8 ∧ low 8 ≠ 7 ∧
      low 8 ≠ 9 ∧ low 9 ≠ 8) →
      ∀ x : Fin 4, x ∈ ({f, a, b, c, d} : Finset (Fin 4)))
    (hright : (low 7 ≠ 8 ∧ low 8 ≠ 7 ∧ low 8 ≠ 9 ∧ low 9 ≠ 8 ∧
      low 9 ≠ 10 ∧ low 10 ≠ 9) →
      ∀ x : Fin 4, x ∈ ({a, b, c, d, e} : Finset (Fin 4))) :
    False := by
  obtain ⟨h67, h76, h78, h87, h89, h98, h9t, ht9⟩ :=
    truncation_twelve_vertex_forced_unselected_path low hcover
  exact six_cycle_three_path_four_color_windows_obstruction a b c d e f
    hde hef hfa hmono1 hmono2 hmatch
    (hleft ⟨h67, h76, h78, h87, h89, h98⟩)
    (hright ⟨h78, h87, h89, h98, h9t, ht9⟩)
