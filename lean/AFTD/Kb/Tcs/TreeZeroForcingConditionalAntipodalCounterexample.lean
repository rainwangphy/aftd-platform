import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans
import AFTD.Kb.Tcs.ZeroForced

/-!
# tree_zero_forcing_conditional_antipodal_counterexample

Topic: graphs   Node: 95239bf4db9b

Provenance: original. Related work: A counterexample to a conditional antipodal-pairs route to OP-1399, arXiv:2611.11352, compared with the criterion in arXiv:0907.0243.

There is a nine-vertex tree and disjoint fixed-white and four-element free sets for which at least one 1–3 partition gives two fort-free sets, while no 2–2 partition does. Thus the fort-free-set family can fail the conditional antipodal-pairs property.
-/

open SimpleGraph

private def ap_witness_edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (0, 5), (2, 3), (3, 4), (5, 6), (5, 8), (6, 7)]

private def ap_witness_graph : SimpleGraph (Fin 9) where
  Adj u v := (u, v) ∈ ap_witness_edges ∨ (v, u) ∈ ap_witness_edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩

private instance : DecidableRel ap_witness_graph.Adj := by
  intro u v
  change Decidable ((u, v) ∈ ap_witness_edges ∨ (v, u) ∈ ap_witness_edges)
  infer_instance

private theorem ap_witness_tree : ap_witness_graph.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · apply (ap_witness_graph.connected_iff_exists_forall_reachable).mpr
    refine ⟨0, ?_⟩
    have h01 : ap_witness_graph.Reachable 0 1 := (show ap_witness_graph.Adj 0 1 by decide).reachable
    have h02 : ap_witness_graph.Reachable 0 2 := h01.trans (show ap_witness_graph.Adj 1 2 by decide).reachable
    have h03 : ap_witness_graph.Reachable 0 3 := h02.trans (show ap_witness_graph.Adj 2 3 by decide).reachable
    have h04 : ap_witness_graph.Reachable 0 4 := h03.trans (show ap_witness_graph.Adj 3 4 by decide).reachable
    have h05 : ap_witness_graph.Reachable 0 5 := (show ap_witness_graph.Adj 0 5 by decide).reachable
    have h06 : ap_witness_graph.Reachable 0 6 := h05.trans (show ap_witness_graph.Adj 5 6 by decide).reachable
    have h07 : ap_witness_graph.Reachable 0 7 := h06.trans (show ap_witness_graph.Adj 6 7 by decide).reachable
    have h08 : ap_witness_graph.Reachable 0 8 := h05.trans (show ap_witness_graph.Adj 5 8 by decide).reachable
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.rfl
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h05
    · exact h06
    · exact h07
    · exact h08
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

private def ap_blue_a : Set (Fin 9) := {0, 2, 3, 6}
private theorem ap_blue_a_forcing : is_zero_forcing_set ap_witness_graph ap_blue_a := by
  have h0 : ZeroForced ap_witness_graph ap_blue_a 0 := ZeroForced.init 0 (by simp [ap_blue_a])
  have h2 : ZeroForced ap_witness_graph ap_blue_a 2 := ZeroForced.init 2 (by simp [ap_blue_a])
  have h3 : ZeroForced ap_witness_graph ap_blue_a 3 := ZeroForced.init 3 (by simp [ap_blue_a])
  have h6 : ZeroForced ap_witness_graph ap_blue_a 6 := ZeroForced.init 6 (by simp [ap_blue_a])
  have h1 : ZeroForced ap_witness_graph ap_blue_a 1 := by
    apply ZeroForced.step 2 1 h2 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h5 : ZeroForced ap_witness_graph ap_blue_a 5 := by
    apply ZeroForced.step 0 5 h0 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h4 : ZeroForced ap_witness_graph ap_blue_a 4 := by
    apply ZeroForced.step 3 4 h3 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h8 : ZeroForced ap_witness_graph ap_blue_a 8 := by
    apply ZeroForced.step 5 8 h5 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h7 : ZeroForced ap_witness_graph ap_blue_a 7 := by
    apply ZeroForced.step 6 7 h6 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  intro v
  fin_cases v <;> assumption

private theorem ap_fort_blocking {V : Type*} (G : SimpleGraph V) (S F : Set V)
    (hdisjoint : ∀ v, v ∈ F → v ∉ S)
    (hfort : ∀ u, u ∉ F → ∀ w, w ∈ F → G.Adj u w →
      ∃ x, x ∈ F ∧ G.Adj u x ∧ x ≠ w) :
    ∀ v, ZeroForced G S v → v ∉ F := by
  intro v hv
  induction hv with
  | init v hvS =>
    intro hvF
    exact hdisjoint v hvF hvS
  | step u w hu huw hothers ihu ihothers =>
    intro hwF
    obtain ⟨x, hxF, hux, hxw⟩ := hfort u ihu w hwF huw
    exact ihothers x hux hxw hxF

private theorem ap_fort_blocks_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W F : Finset V) (hsub : F ⊆ W) (hne : F.Nonempty)
    (hfort : ∀ u, u ∉ F → ∀ w, w ∈ F → G.Adj u w →
      ∃ x, x ∈ F ∧ G.Adj u x ∧ x ≠ w) :
    ¬ is_zero_forcing_set G ((Finset.univ \ W : Finset V) : Set V) := by
  intro hS
  obtain ⟨v, hv⟩ := hne
  have hdisj : ∀ v, v ∈ (F : Set V) → v ∉ ((Finset.univ \ W : Finset V) : Set V) := by
    intro x hxF hxS
    exact (Finset.mem_sdiff.mp hxS).2 (hsub hxF)
  have hf : ∀ u, u ∉ (F : Set V) → ∀ w, w ∈ (F : Set V) → G.Adj u w →
      ∃ x, x ∈ (F : Set V) ∧ G.Adj u x ∧ x ≠ w := hfort
  exact ap_fort_blocking G ((Finset.univ \ W : Finset V) : Set V) (F : Set V) hdisj hf v (hS v) hv

private def ap_blue_c : Set (Fin 9) := {0, 7}

private theorem ap_blue_c_forcing : is_zero_forcing_set ap_witness_graph ap_blue_c := by
  have h0 : ZeroForced ap_witness_graph ap_blue_c 0 := ZeroForced.init 0 (by simp [ap_blue_c])
  have h7 : ZeroForced ap_witness_graph ap_blue_c 7 := ZeroForced.init 7 (by simp [ap_blue_c])
  have h6 : ZeroForced ap_witness_graph ap_blue_c 6 := by
    apply ZeroForced.step 7 6 h7 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h5 : ZeroForced ap_witness_graph ap_blue_c 5 := by
    apply ZeroForced.step 6 5 h6 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h1 : ZeroForced ap_witness_graph ap_blue_c 1 := by
    apply ZeroForced.step 0 1 h0 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h2 : ZeroForced ap_witness_graph ap_blue_c 2 := by
    apply ZeroForced.step 1 2 h1 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h3 : ZeroForced ap_witness_graph ap_blue_c 3 := by
    apply ZeroForced.step 2 3 h2 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h4 : ZeroForced ap_witness_graph ap_blue_c 4 := by
    apply ZeroForced.step 3 4 h3 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  have h8 : ZeroForced ap_witness_graph ap_blue_c 8 := by
    apply ZeroForced.step 5 8 h5 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [ap_witness_graph, ap_witness_edges]
  intro v
  fin_cases v <;> assumption

private def ap_fixed_white : Finset (Fin 9) := {1, 4, 5, 8}
private def ap_free_vertices : Finset (Fin 9) := {2, 3, 6, 7}

private theorem ap_bad_if_seven (X : Finset (Fin 9)) (hsub : X ⊆ ap_free_vertices)
    (hcard : X.card = 2) (h7 : (7 : Fin 9) ∈ X) :
    ¬ is_zero_forcing_set ap_witness_graph
      ((Finset.univ \ (ap_fixed_white ∪ X) : Finset (Fin 9)) : Set (Fin 9)) := by
  have ho : (2 : Fin 9) ∈ X ∨ (3 : Fin 9) ∈ X ∨ (6 : Fin 9) ∈ X := by
    by_contra hn
    push_neg at hn
    have hs : X ⊆ ({7} : Finset (Fin 9)) := by
      intro v hv
      have hmem := hsub hv
      fin_cases v <;> simp_all [ap_free_vertices]
    have hc := Finset.card_le_card hs
    simp at hc
    omega
  rcases ho with h2 | h3 | h6
  · apply ap_fort_blocks_complement ap_witness_graph _ ({1, 2, 4, 5, 7, 8} : Finset (Fin 9))
    · intro v hv
      fin_cases v <;> simp_all [ap_fixed_white]
    · decide
    · decide
  · apply ap_fort_blocks_complement ap_witness_graph _ ({1, 3, 4, 5, 7, 8} : Finset (Fin 9))
    · intro v hv
      fin_cases v <;> simp_all [ap_fixed_white]
    · decide
    · decide
  · apply ap_fort_blocks_complement ap_witness_graph _ ({6, 7, 8} : Finset (Fin 9))
    · intro v hv
      fin_cases v <;> simp_all [ap_fixed_white]
    · decide
    · decide

theorem tree_zero_forcing_conditional_antipodal_counterexample : ∃ (G : SimpleGraph (Fin 9)) (A F : Finset (Fin 9)),
    G.IsTree ∧ Disjoint A F ∧ F.card = 4 ∧
    (∃ S : Finset (Fin 9), S ⊆ F ∧ S.card = 1 ∧
      is_zero_forcing_set G ((Finset.univ \ (A ∪ S) : Finset (Fin 9)) : Set (Fin 9)) ∧
      is_zero_forcing_set G ((Finset.univ \ (A ∪ (F \ S)) : Finset (Fin 9)) : Set (Fin 9))) ∧
    (∀ S : Finset (Fin 9), S ⊆ F → S.card = 2 →
      ¬ (is_zero_forcing_set G ((Finset.univ \ (A ∪ S) : Finset (Fin 9)) : Set (Fin 9)) ∧
         is_zero_forcing_set G ((Finset.univ \ (A ∪ (F \ S)) : Finset (Fin 9)) : Set (Fin 9)))) := by
  refine ⟨ap_witness_graph, ap_fixed_white, ap_free_vertices, ap_witness_tree, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨{7}, ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · have hs : ((Finset.univ \ (ap_fixed_white ∪ {7}) : Finset (Fin 9)) : Set (Fin 9)) = ap_blue_a := by
        ext v
        fin_cases v <;> simp [ap_fixed_white, ap_blue_a]
      rw [hs]
      exact ap_blue_a_forcing
    · have hs : ((Finset.univ \ (ap_fixed_white ∪ (ap_free_vertices \ {7})) : Finset (Fin 9)) : Set (Fin 9)) = ap_blue_c := by
        ext v
        fin_cases v <;> simp [ap_fixed_white, ap_free_vertices, ap_blue_c]
      rw [hs]
      exact ap_blue_c_forcing
  · intro S hS hc ⟨h1, h2⟩
    by_cases h7 : (7 : Fin 9) ∈ S
    · exact ap_bad_if_seven S hS hc h7 h1
    · have h7' : (7 : Fin 9) ∈ ap_free_vertices \ S := by simp [ap_free_vertices, h7]
      have hsub : ap_free_vertices \ S ⊆ ap_free_vertices := Finset.sdiff_subset
      have hcard : (ap_free_vertices \ S).card = 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS]
        simp [ap_free_vertices, hc]
      exact ap_bad_if_seven (ap_free_vertices \ S) hsub hcard h7' h2
