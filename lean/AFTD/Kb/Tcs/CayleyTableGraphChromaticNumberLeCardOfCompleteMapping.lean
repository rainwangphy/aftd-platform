import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph
import AFTD.Kb.Tcs.GroupIsCompleteMapping

/-!
# cayley_table_graph_chromatic_number_le_card_of_complete_mapping

Topic: combinatorics   Node: c529d8efaaea

Provenance: formalization of a published result. Source: arXiv:2611.13274 Theorem 2.10, Theorem 2.14

If a finite group G admits a complete mapping, then the chromatic number of its Cayley table graph is at most |G|.
-/

/-- A complete mapping yields a proper |G|-coloring of the Cayley table graph. -/
theorem cayley_table_graph_chromatic_number_le_card_of_complete_mapping
    (G : Type*) [Group G] [Fintype G] (θ : G → G) (hθ : group_is_complete_mapping θ) :
    (cayley_table_graph G).chromaticNumber ≤ Fintype.card G := by
  obtain ⟨hθbij, hprod⟩ := hθ
  -- Color the cell (x, y) by (θ x)⁻¹ * y ∈ G.
  let color : G × G → Fin (Fintype.card G) := fun p => Fintype.equivFin G ((θ p.1)⁻¹ * p.2)
  -- Cells with the same color and the same product symbol coincide.
  have hkey : ∀ p q : G × G, (θ p.1)⁻¹ * p.2 = (θ q.1)⁻¹ * q.2 →
      p.1 * p.2 = q.1 * q.2 → p = q := by
    intro p q hc hp
    have h1 : p.1 * θ p.1 = q.1 * θ q.1 := by
      have e1 : p.1 * θ p.1 = p.1 * p.2 * ((θ p.1)⁻¹ * p.2)⁻¹ := by group
      have e2 : q.1 * θ q.1 = q.1 * q.2 * ((θ q.1)⁻¹ * q.2)⁻¹ := by group
      rw [e1, e2, hc, hp]
    have hx : p.1 = q.1 := hprod.injective h1
    have hy : p.2 = q.2 := by
      have e1 : p.2 = θ p.1 * ((θ p.1)⁻¹ * p.2) := by group
      have e2 : q.2 = θ q.1 * ((θ q.1)⁻¹ * q.2) := by group
      rw [e1, e2, hc, hx]
    exact Prod.ext hx hy
  refine SimpleGraph.Colorable.chromaticNumber_le ⟨⟨color, ?_⟩⟩
  intro u v hadj hcol
  apply hadj.1
  have hcu : (θ u.1)⁻¹ * u.2 = (θ v.1)⁻¹ * v.2 := (Fintype.equivFin G).injective hcol
  rcases hadj.2 with h | h | h
  · -- common row: u.1 = v.1, cancel (θ u.1)⁻¹
    have hy : u.2 = v.2 := by
      have e1 : u.2 = θ u.1 * ((θ u.1)⁻¹ * u.2) := by group
      have e2 : v.2 = θ v.1 * ((θ v.1)⁻¹ * v.2) := by group
      rw [e1, e2, hcu, h]
    exact Prod.ext h hy
  · -- common column: u.2 = v.2, cancel u.2 on the right, then use injectivity of θ
    have hx : u.1 = v.1 := by
      have h2 : (θ u.1)⁻¹ = (θ v.1)⁻¹ := by
        rw [← h] at hcu
        exact mul_right_cancel hcu
      exact hθbij.injective (inv_injective h2)
    exact Prod.ext hx h
  · -- common product symbol
    exact hkey u v hcu h
