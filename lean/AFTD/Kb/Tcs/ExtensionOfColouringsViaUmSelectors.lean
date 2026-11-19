import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsUmSelector
import AFTD.Kb.Tcs.SimpleGraphUmSelectorExtension
import AFTD.Kb.Tcs.SimpleGraphIsIumcColoring
import AFTD.Kb.Tcs.SimpleGraphIsIumoColoring
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# extension_of_colourings_via_um_selectors

Topic: graphs   Node: 34ff562f5b31

Provenance: formalization of a published result. Source: arXiv:2611.23478 Lemma 5

Let G be a graph on vertex type V. Let S be a subset of V and let φ : S → Fin p be such that (S, φ) is a UM-selector in G of width p. Let ψ : Sᶜ → Fin q be a colouring of the induced subgraph G - S. Then the extension colouring σ = simple_graph_um_selector_extension S φ ψ is an iUMc-colouring of G. If G has no isolated vertices and for every s ∈ S the maximum colour of ψ on N(s) is attained exactly once, then σ is also an iUMo-colouring of G. Furthermore, if ψ is a proper colouring of G - S, then σ is a proper colouring of G.
-/

lemma extension_of_colourings_via_um_selectors_ext_in {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) {v : V} (h : v ∈ S) :
    simple_graph_um_selector_extension S φ ψ v = Fin.natAdd q (φ ⟨v, h⟩) := by
  unfold simple_graph_um_selector_extension
  rw [dif_pos h]

lemma extension_of_colourings_via_um_selectors_ext_not_in {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) {v : V} (h : v ∉ S) :
    simple_graph_um_selector_extension S φ ψ v = Fin.castAdd p (ψ ⟨v, h⟩) := by
  unfold simple_graph_um_selector_extension
  rw [dif_neg h]

lemma extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_mem {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) {u w : V} (hu : u ∉ S) (hw : w ∈ S) :
    simple_graph_um_selector_extension S φ ψ u < simple_graph_um_selector_extension S φ ψ w := by
  rw [simple_graph_um_selector_extension, dif_neg hu,
      simple_graph_um_selector_extension, dif_pos hw]
  rw [Fin.lt_def]
  have := (ψ ⟨u, hu⟩).isLt
  have := (φ ⟨w, hw⟩).isLt
  have h1 : (Fin.castAdd p (ψ ⟨u, hu⟩) : Fin (q + p)).val = (ψ ⟨u, hu⟩).val := Fin.val_castAdd p _
  have h2 : (Fin.natAdd q (φ ⟨w, hw⟩) : Fin (q + p)).val = q + (φ ⟨w, hw⟩).val := Fin.val_natAdd q _
  omega

lemma extension_of_colourings_via_um_selectors_ext_lt_of_mem_mem {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) {u w : V} (hu : u ∈ S) (hw : w ∈ S) :
    simple_graph_um_selector_extension S φ ψ u < simple_graph_um_selector_extension S φ ψ w ↔
      φ ⟨u, hu⟩ < φ ⟨w, hw⟩ := by
  rw [simple_graph_um_selector_extension, dif_pos hu,
      simple_graph_um_selector_extension, dif_pos hw]
  exact Fin.natAdd_lt_natAdd_iff q

lemma extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_not_mem {V : Type*} (S : Set V) {p q : ℕ}
    (φ : ↥S → Fin p) (ψ : ↥(Sᶜ) → Fin q) {u w : V} (hu : u ∉ S) (hw : w ∉ S) :
    simple_graph_um_selector_extension S φ ψ u < simple_graph_um_selector_extension S φ ψ w ↔
      ψ ⟨u, hu⟩ < ψ ⟨w, hw⟩ := by
  rw [simple_graph_um_selector_extension, dif_neg hu,
      simple_graph_um_selector_extension, dif_neg hw]
  exact (Fin.strictMono_castAdd p).lt_iff_lt

/-- Lemma 5: Extension of colourings via unique-maximum selectors into iUMc-, iUMo-, and proper colourings. -/
theorem extension_of_colourings_via_um_selectors {V : Type*} (G : SimpleGraph V) {p q : ℕ}
    (S : Set V) (φ : ↥S → Fin p) (hφ : simple_graph_is_um_selector G S φ)
    (ψ : ↥(Sᶜ) → Fin q) :
    simple_graph_is_iumc_coloring G (simple_graph_um_selector_extension S φ ψ) ∧
    ((∀ v : V, ¬ G.IsIsolated v) →
      (∀ s : ↥S, ∃ u : ↥(Sᶜ), G.Adj s.1 u.1 ∧ ∀ w : ↥(Sᶜ), G.Adj s.1 w.1 → w ≠ u → ψ w < ψ u) →
      simple_graph_is_iumo_coloring G (simple_graph_um_selector_extension S φ ψ)) ∧
    ((∀ (u v : ↥(Sᶜ)), (G.induce Sᶜ).Adj u v → ψ u ≠ ψ v) →
      ∀ {u v : V}, G.Adj u v →
        simple_graph_um_selector_extension S φ ψ u ≠ simple_graph_um_selector_extension S φ ψ v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rcases hφ.2 v with ⟨u, hu_mem, hu_max⟩
    refine ⟨u.1, hu_mem, ?_⟩
    intro w hw_mem hwu
    by_cases hwS : w ∈ S
    · have h_ne : (⟨w, hwS⟩ : ↥S) ≠ u := by
        intro h_eq
        apply hwu
        exact congr_arg Subtype.val h_eq
      have h_lt := hu_max ⟨w, hwS⟩ hw_mem h_ne
      rwa [extension_of_colourings_via_um_selectors_ext_lt_of_mem_mem S φ ψ hwS u.2]
    · exact extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_mem S φ ψ hwS u.2
  · intros _h_no_iso h_max v
    by_cases hv : v ∈ S
    · rcases h_max ⟨v, hv⟩ with ⟨u, hu_adj, hu_max⟩
      refine ⟨u.1, hu_adj, ?_⟩
      intro w hw_adj hwu
      have hwS : w ∉ S := by
        intro hwS
        exact hφ.1 hv hwS hw_adj.ne hw_adj
      have h_ne : (⟨w, hwS⟩ : ↥(Sᶜ)) ≠ u := by
        intro h_eq
        apply hwu
        exact congr_arg Subtype.val h_eq
      have h_lt := hu_max ⟨w, hwS⟩ hw_adj h_ne
      rwa [extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_not_mem S φ ψ hwS u.2]
    · rcases hφ.2 v with ⟨u, hu_mem, hu_max⟩
      have hu_ne_v : u.1 ≠ v := by
        rintro rfl
        exact hv u.2
      have hu_adj : u.1 ∈ G.neighborSet v := by
        rcases Set.mem_insert_iff.mp hu_mem with rfl | h
        · exact (hu_ne_v rfl).elim
        · exact h
      refine ⟨u.1, hu_adj, ?_⟩
      intro w hw_adj hwu
      by_cases hwS : w ∈ S
      · have h_ne : (⟨w, hwS⟩ : ↥S) ≠ u := by
          intro h_eq
          apply hwu
          exact congr_arg Subtype.val h_eq
        have hw_mem : w ∈ insert v (G.neighborSet v) := Set.mem_insert_of_mem _ hw_adj
        have h_lt := hu_max ⟨w, hwS⟩ hw_mem h_ne
        rwa [extension_of_colourings_via_um_selectors_ext_lt_of_mem_mem S φ ψ hwS u.2]
      · exact extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_mem S φ ψ hwS u.2
  · intro hψ u v hadj
    by_cases hu : u ∈ S
    · by_cases hv : v ∈ S
      · exact (hφ.1 hu hv hadj.ne hadj).elim
      · intro h_eq
        have := extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_mem S φ ψ hv hu
        rw [h_eq] at this
        exact lt_irrefl _ this
    · by_cases hv : v ∈ S
      · intro h_eq
        have := extension_of_colourings_via_um_selectors_ext_lt_of_not_mem_mem S φ ψ hu hv
        rw [h_eq] at this
        exact lt_irrefl _ this
      · intro h_eq
        have hadj' : (G.induce Sᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ := G.induce_adj.mpr hadj
        have hne := hψ ⟨u, hu⟩ ⟨v, hv⟩ hadj'
        rw [extension_of_colourings_via_um_selectors_ext_not_in S φ ψ hu,
            extension_of_colourings_via_um_selectors_ext_not_in S φ ψ hv] at h_eq
        have : ψ ⟨u, hu⟩ = ψ ⟨v, hv⟩ := Fin.castAdd_inj.mp h_eq
        exact hne this
