import AFTD.Prelude
import AFTD.Kb.Tcs.Op258HasMonoClique

/-!
# op_258_no_mono_triangle_of_layering

Topic: combinatorics   Node: 25bb354fc771

Provenance: helper lemma. step towards op_258_sum_ne_top_of_forces_three

If an edge colouring c of K_n is subordinate to a bipartite edge layering (so each colour lives in a layer whose endpoints have distinct values under a 2-colouring), then c contains no monochromatic triangle K_3.
-/

/-- An edge colouring subordinate to a family of bipartite layers has no monochromatic K_3. -/
theorem op_258_no_mono_triangle_of_layering (n : ℕ) (l : ℕ)
    (layer : (SimpleGraph.completeGraph (Fin n)).edgeSet → Fin l)
    (f : Fin l → Fin n → Fin 2)
    (h_bip : ∀ (u v : Fin n) (hne : u ≠ v),
      f (layer ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩) u ≠
      f (layer ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩) v)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (col_layer : ℕ+ → Fin l)
    (hc_layer : ∀ e, col_layer (c e) = layer e) :
    ¬ op_258_has_mono_clique n c 3 := by
  rintro ⟨s, i, hcard, hmono⟩
  have key : ∀ (u v : Fin n) (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v),
      f (col_layer i) u ≠ f (col_layer i) v := by
    intro u v hu hv hne
    have hcv : c ⟨s(u,v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩ = i := hmono hu hv hne
    have hl : layer ⟨s(u,v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩ = col_layer i := by
      rw [← hc_layer ⟨s(u,v), by simp [SimpleGraph.completeGraph_eq_top, hne]⟩, hcv]
    simpa [hl] using h_bip u v hne
  have hinj : Function.Injective (fun x : s => f (col_layer i) (x : Fin n)) := by
    intro x y hxy
    by_contra hne
    exact key (x : Fin n) (y : Fin n) x.property y.property (fun h => hne (Subtype.ext h)) hxy
  have hle := Fintype.card_le_of_injective (fun x : s => f (col_layer i) (x : Fin n)) hinj
  simp only [Fintype.card_coe, Fintype.card_fin] at hle
  omega
