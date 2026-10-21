import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAchromaticNumber
import AFTD.Kb.Tcs.SimpleGraphColoringIsAchromatic

/-!
# simple_graph_achromatic_number_le_max_degree_or_half

Topic: graphs   Node: 353957fc4fc6

Provenance: formalization of a published result. Source: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs), Proposition 3.1 (stated there for the pseudochromatic number, which is at least χ_a; the Lean is the achromatic case)

For every finite graph, χ_a(G) ≤ max{Δ(G) + 1, ⌊n/2⌋}: if some colour class is a single vertex, that vertex has a neighbour in each of the other classes; otherwise every class has at least two vertices.
-/

theorem simple_graph_achromatic_number_le_max_degree_or_half {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    simple_graph_achromatic_number G ≤ max (G.maxDegree + 1) (Fintype.card V / 2) := by
  dsimp [simple_graph_achromatic_number]
  apply csSup_le'
  rintro k ⟨C, hC⟩
  by_cases h : ∃ i : Fin k, (Finset.univ.filter (fun a => C a = i)).card ≤ 1
  · obtain ⟨i, hi⟩ := h
    obtain ⟨v, hv⟩ := hC.1 i
    have hv_mem : v ∈ Finset.univ.filter (fun a => C a = i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ v, hv⟩
    have h_unique : ∀ u, C u = i → u = v := by
      intro u hu
      have hu_mem : u ∈ Finset.univ.filter (fun a => C a = i) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ u, hu⟩
      exact Finset.card_le_one_iff.mp hi hu_mem hv_mem
    have h_subset : ∀ j ∈ Finset.univ.erase i, ∃ w ∈ G.neighborFinset v, C w = j := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hij : i ≠ j := hji.symm
      obtain ⟨u, w, hadj, hCu, hCw⟩ := hC.2 i j hij
      have hu : u = v := h_unique u hCu
      subst hu
      refine ⟨w, ?_, hCw⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj
    have h_card_le : (Finset.univ.erase i).card ≤ (G.neighborFinset v).card := by
      have : Finset.univ.erase i ⊆ (G.neighborFinset v).image C := by
        intro j hj
        obtain ⟨w, hw, rfl⟩ := h_subset j hj
        exact Finset.mem_image_of_mem C hw
      exact (Finset.card_le_card this).trans Finset.card_image_le
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h_card_le
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h_card_le
    have h_deg : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
    have hk : k ≤ G.maxDegree + 1 := by omega
    exact le_trans hk (le_max_left _ _)
  · have h2 : ∀ i : Fin k, 2 ≤ (Finset.univ.filter (fun a => C a = i)).card := by
      intro i
      have : ¬ (Finset.univ.filter (fun a => C a = i)).card ≤ 1 := fun hle => h ⟨i, hle⟩
      omega
    have h_sum : Fintype.card V = ∑ b : Fin k, (Finset.univ.filter (fun a => C a = b)).card := by
      exact Finset.card_eq_sum_card_fiberwise (f := C) (fun _ _ => Finset.mem_univ _)
    have h_le : (∑ b : Fin k, 2) ≤ ∑ b : Fin k, (Finset.univ.filter (fun a => C a = b)).card := by
      apply Finset.sum_le_sum
      intro i _
      exact h2 i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_le
    rw [← h_sum] at h_le
    have hk : k ≤ Fintype.card V / 2 := by omega
    exact le_trans hk (le_max_right _ _)
