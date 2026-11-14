import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.SupportGraph

/-!
# set_coloring_ramsey_property_mono_N

Topic: combinatorics   Node: 305d3ba22c7e

Provenance: helper lemma. folklore

For any simple graph G, palette size r, edge subset size s, intersection parameter t, and natural numbers N ≤ M, if every (r, s)-set-coloring of K_N contains a t-monochromatic copy of G, then every (r, s)-set-coloring of K_M also contains a t-monochromatic copy of G.
-/

/-- Monotonicity of the set-coloring Ramsey property in the number of vertices. -/
theorem set_coloring_ramsey_property_mono_N {V : Type*} (G : SimpleGraph V) (r s t : ℕ)
    {N M : ℕ} (hNM : N ≤ M) (h : set_coloring_ramsey_property G r s t N) :
    set_coloring_ramsey_property G r s t M := by
  classical
  intro φ hφ
  let f : Fin N ↪ Fin M := Fin.castLEEmb hNM
  let φN : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r) :=
    fun e => φ ((SimpleGraph.Embedding.completeGraph f).mapEdgeSet e)
  have hφN : ∀ e, (φN e).card = s := fun e => hφ _
  obtain ⟨T, hTcard, hcopy⟩ := h φN hφN
  refine ⟨T, hTcard, ?_⟩
  have hle : support_graph φN T ≤ (support_graph φ T).comap f := by
    intro u v huv
    simp only [SimpleGraph.comap_adj]
    simp only [support_graph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq] at huv ⊢
    rcases huv with ⟨⟨hN, hsub⟩, hne⟩
    let eN : (⊤ : SimpleGraph (Fin N)).edgeSet := ⟨s(u, v), hN⟩
    let eM : (⊤ : SimpleGraph (Fin M)).edgeSet :=
      (SimpleGraph.Embedding.completeGraph f).mapEdgeSet eN
    have heq : eM = ⟨s(f u, f v), eM.property⟩ := by
      apply Subtype.ext
      dsimp [eM, eN]
      simp [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet, Sym2.map_mk]
    refine ⟨⟨eM.property, ?_⟩, ?_⟩
    · show T ⊆ φ ⟨s(f u, f v), eM.property⟩
      rw [← heq]
      exact hsub
    · intro h
      exact hne (f.injective h)
  rcases hcopy with ⟨c⟩
  exact ⟨(SimpleGraph.Embedding.comap f (support_graph φ T)).toCopy.comp
    ((SimpleGraph.Copy.ofLE (support_graph φN T) ((support_graph φ T).comap f) hle).comp c)⟩
