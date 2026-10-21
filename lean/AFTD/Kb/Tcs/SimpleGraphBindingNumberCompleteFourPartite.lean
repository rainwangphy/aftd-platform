import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphBindingNumber
import AFTD.Kb.Tcs.SimpleGraphBindingNumberLeIff

/-!
# simple_graph_binding_number_complete_four_partite

Topic: graphs   Node: c7dfdb073dbf

Provenance: formalization of a published result. Source: arXiv:2610.28536 (A sharp bound on the binding number of K_k-free graphs and the Brandt conjecture), Sec. 1: the bound k − 2 is attained by complete (k−1)-partite graphs with equal parts (case k = 5)

The complete 4-partite graph with four parts of size m ≥ 1 is K_5-free and has binding number exactly 3, so the bound 3 conjectured for K_5-free graphs would be sharp.
-/

lemma simple_graph_binding_number_complete_four_partite_card_filter_eq (m : ℕ) (i : Fin 4) :
    (Finset.filter (fun u : (Σ _ : Fin 4, Fin m) => u.1 = i) Finset.univ).card = m := by
  have h : (Finset.filter (fun u : (Σ _ : Fin 4, Fin m) => u.1 = i) Finset.univ) =
    (Finset.univ : Finset (Fin m)).map ⟨fun x => ⟨i, x⟩, fun x y h => by injections⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro rfl; exact ⟨b, rfl⟩
    · rintro ⟨c, hc⟩; injection hc with h1 h2; exact h1.symm
  rw [h]
  simp

lemma simple_graph_binding_number_complete_four_partite_card_filter_ne (m : ℕ) (i : Fin 4) :
    (Finset.filter (fun u : (Σ _ : Fin 4, Fin m) => u.1 ≠ i) Finset.univ).card = 3 * m := by
  have h_not : (Finset.filter (fun u : (Σ _ : Fin 4, Fin m) => u.1 ≠ i) Finset.univ) =
      Finset.univ \ Finset.filter (fun u : (Σ _ : Fin 4, Fin m) => u.1 = i) Finset.univ := by
    exact Finset.filter_not (fun u : (Σ _ : Fin 4, Fin m) => u.1 = i) Finset.univ
  rw [h_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  rw [simple_graph_binding_number_complete_four_partite_card_filter_eq]
  simp
  omega

lemma simple_graph_binding_number_complete_four_partite_card_le_of_all_fst_eq {m : ℕ} {S : Finset (Σ _ : Fin 4, Fin m)} {i : Fin 4}
    (hi : ∀ v ∈ S, v.1 = i) : S.card ≤ m := by
  have h_sub : S ⊆ Finset.filter (fun u => u.1 = i) Finset.univ := by
    intro v hv
    simp [hi v hv]
  have := Finset.card_le_card h_sub
  rw [simple_graph_binding_number_complete_four_partite_card_filter_eq] at this
  exact this

lemma simple_graph_binding_number_complete_four_partite_all_fst_eq_of_ne_univ {m : ℕ} {S : Finset (Σ _ : Fin 4, Fin m)}
    (huniv : S.biUnion (fun v => (SimpleGraph.completeMultipartiteGraph (fun _ : Fin 4 => Fin m)).neighborFinset v) ≠ Finset.univ) :
    ∃ i : Fin 4, ∀ v ∈ S, v.1 = i := by
  by_contra! h
  apply huniv
  rw [Finset.eq_univ_iff_forall]
  intro u
  rw [Finset.mem_biUnion]
  obtain ⟨v, hvS, hvu⟩ := h u.1
  exact ⟨v, hvS, by rwa [SimpleGraph.mem_neighborFinset]⟩

lemma simple_graph_binding_number_complete_four_partite_biUnion_neighborFinset_eq_of_all_fst_eq {m : ℕ} {S : Finset (Σ _ : Fin 4, Fin m)}
    (hne : S.Nonempty) {i : Fin 4} (hi : ∀ v ∈ S, v.1 = i) :
    S.biUnion (fun v => (SimpleGraph.completeMultipartiteGraph (fun _ : Fin 4 => Fin m)).neighborFinset v) =
      Finset.filter (fun u => u.1 ≠ i) Finset.univ := by
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset, SimpleGraph.completeMultipartiteGraph, SimpleGraph.comap_adj, SimpleGraph.top_adj]
  constructor
  · rintro ⟨v, hvS, hvu⟩
    rw [hi v hvS] at hvu
    exact hvu.symm
  · intro hu
    obtain ⟨v, hvS⟩ := hne
    exact ⟨v, hvS, by rw [hi v hvS]; exact hu.symm⟩

theorem simple_graph_binding_number_complete_four_partite (m : ℕ) (hm : 1 ≤ m) :
    simple_graph_binding_number
      (SimpleGraph.completeMultipartiteGraph (fun _ : Fin 4 => Fin m)) = 3 ∧
    (SimpleGraph.completeMultipartiteGraph (fun _ : Fin 4 => Fin m)).CliqueFree 5 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty ((_ : Fin 4) × Fin m) := ⟨⟨0, ⟨0, hm⟩⟩⟩
  set G := SimpleGraph.completeMultipartiteGraph (fun _ : Fin 4 => Fin m)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [simple_graph_binding_number_le_iff]
    let S : Finset ((_ : Fin 4) × Fin m) := Finset.filter (fun u => u.1 = (0 : Fin 4)) Finset.univ
    have hS_mem : (⟨0, ⟨0, hm⟩⟩ : (Σ _ : Fin 4, Fin m)) ∈ S := by simp [S]
    have hSne : S.Nonempty := ⟨⟨0, ⟨0, hm⟩⟩, hS_mem⟩
    have hSi : ∀ v ∈ S, v.1 = (0 : Fin 4) := by
      intro v hv
      simp only [S, Finset.mem_filter] at hv
      exact hv.2
    have hSN : S.biUnion (fun v => G.neighborFinset v) = Finset.filter (fun u => u.1 ≠ (0 : Fin 4)) Finset.univ :=
      simple_graph_binding_number_complete_four_partite_biUnion_neighborFinset_eq_of_all_fst_eq hSne hSi
    refine ⟨S, hSne, ?_, ?_⟩
    · rw [hSN]
      intro h_univ
      have : (⟨0, ⟨0, hm⟩⟩ : (Σ _ : Fin 4, Fin m)) ∈ Finset.univ := Finset.mem_univ _
      rw [← h_univ] at this
      simp at this
    · rw [hSN, simple_graph_binding_number_complete_four_partite_card_filter_ne,
          simple_graph_binding_number_complete_four_partite_card_filter_eq]
      push_cast
      linarith
  · have : Nonempty { S : Finset ((_ : Fin 4) × Fin m) // S.Nonempty ∧ S.biUnion (fun v => G.neighborFinset v) ≠ Finset.univ } := by
      refine ⟨⟨{⟨0, ⟨0, hm⟩⟩}, Finset.singleton_nonempty _, ?_⟩⟩
      intro heq
      have hnv : (⟨0, ⟨0, hm⟩⟩ : (Σ _ : Fin 4, Fin m)) ∉ ({⟨0, ⟨0, hm⟩⟩} : Finset _).biUnion (fun u => G.neighborFinset u) := by simp
      rw [heq] at hnv
      exact hnv (Finset.mem_univ _)
    dsimp [simple_graph_binding_number]
    apply le_ciInf
    rintro ⟨S, hSne, hSuniv⟩
    change 3 ≤ ((S.biUnion (fun v => G.neighborFinset v)).card : ℝ) / S.card
    obtain ⟨i, hi⟩ := simple_graph_binding_number_complete_four_partite_all_fst_eq_of_ne_univ hSuniv
    have hSN : S.biUnion (fun v => G.neighborFinset v) = Finset.filter (fun u => u.1 ≠ i) Finset.univ :=
      simple_graph_binding_number_complete_four_partite_biUnion_neighborFinset_eq_of_all_fst_eq hSne hi
    rw [hSN, simple_graph_binding_number_complete_four_partite_card_filter_ne]
    have h1 : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hSne.card_pos
    have h2 : (S.card : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (simple_graph_binding_number_complete_four_partite_card_le_of_all_fst_eq hi)
    rw [le_div_iff₀ h1]
    push_cast
    linarith
  · apply SimpleGraph.cliqueFree_completeMultipartiteGraph
    decide
