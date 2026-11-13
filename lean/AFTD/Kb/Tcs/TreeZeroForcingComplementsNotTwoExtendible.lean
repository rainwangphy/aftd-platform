import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingComplementsTwoExtendible
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# tree_zero_forcing_complements_not_two_extendible

Topic: graphs   Node: 12b8fa7b2bde

Provenance: original. Related work: A computationally discovered obstruction to using intersection-of-two-matroids for OP-1399. The two-matroid independent-set coefficient result is described in arXiv:2608.23262.

There is a tree on nine vertices whose complements of zero forcing sets are not two-extendible.
-/

open SimpleGraph

private def witness_edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (0, 5), (2, 3), (3, 4), (5, 6), (5, 8), (6, 7)]

private def witness_graph : SimpleGraph (Fin 9) where
  Adj u v := (u, v) ∈ witness_edges ∨ (v, u) ∈ witness_edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v; fin_cases v <;> decide⟩

private instance : DecidableRel witness_graph.Adj := by
  intro u v
  change Decidable ((u, v) ∈ witness_edges ∨ (v, u) ∈ witness_edges)
  infer_instance

private theorem witness_tree : witness_graph.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · apply (witness_graph.connected_iff_exists_forall_reachable).mpr
    refine ⟨0, ?_⟩
    have h01 : witness_graph.Reachable 0 1 := (show witness_graph.Adj 0 1 by decide).reachable
    have h02 : witness_graph.Reachable 0 2 := h01.trans (show witness_graph.Adj 1 2 by decide).reachable
    have h03 : witness_graph.Reachable 0 3 := h02.trans (show witness_graph.Adj 2 3 by decide).reachable
    have h04 : witness_graph.Reachable 0 4 := h03.trans (show witness_graph.Adj 3 4 by decide).reachable
    have h05 : witness_graph.Reachable 0 5 := (show witness_graph.Adj 0 5 by decide).reachable
    have h06 : witness_graph.Reachable 0 6 := h05.trans (show witness_graph.Adj 5 6 by decide).reachable
    have h07 : witness_graph.Reachable 0 7 := h06.trans (show witness_graph.Adj 6 7 by decide).reachable
    have h08 : witness_graph.Reachable 0 8 := h05.trans (show witness_graph.Adj 5 8 by decide).reachable
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

private def blue_a : Set (Fin 9) := {0, 2, 3, 6}
private def blue_b : Set (Fin 9) := {0, 8}

private theorem blue_a_forcing : is_zero_forcing_set witness_graph blue_a := by
  have h0 : ZeroForced witness_graph blue_a 0 := ZeroForced.init 0 (by simp [blue_a])
  have h2 : ZeroForced witness_graph blue_a 2 := ZeroForced.init 2 (by simp [blue_a])
  have h3 : ZeroForced witness_graph blue_a 3 := ZeroForced.init 3 (by simp [blue_a])
  have h6 : ZeroForced witness_graph blue_a 6 := ZeroForced.init 6 (by simp [blue_a])
  have h1 : ZeroForced witness_graph blue_a 1 := by
    apply ZeroForced.step 2 1 h2 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h5 : ZeroForced witness_graph blue_a 5 := by
    apply ZeroForced.step 0 5 h0 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h4 : ZeroForced witness_graph blue_a 4 := by
    apply ZeroForced.step 3 4 h3 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h8 : ZeroForced witness_graph blue_a 8 := by
    apply ZeroForced.step 5 8 h5 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h7 : ZeroForced witness_graph blue_a 7 := by
    apply ZeroForced.step 6 7 h6 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  intro v
  fin_cases v <;> assumption

private theorem blue_b_forcing : is_zero_forcing_set witness_graph blue_b := by
  have h0 : ZeroForced witness_graph blue_b 0 := ZeroForced.init 0 (by simp [blue_b])
  have h8 : ZeroForced witness_graph blue_b 8 := ZeroForced.init 8 (by simp [blue_b])
  have h5 : ZeroForced witness_graph blue_b 5 := by
    apply ZeroForced.step 8 5 h8 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h1 : ZeroForced witness_graph blue_b 1 := by
    apply ZeroForced.step 0 1 h0 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h2 : ZeroForced witness_graph blue_b 2 := by
    apply ZeroForced.step 1 2 h1 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h3 : ZeroForced witness_graph blue_b 3 := by
    apply ZeroForced.step 2 3 h2 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h4 : ZeroForced witness_graph blue_b 4 := by
    apply ZeroForced.step 3 4 h3 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h6 : ZeroForced witness_graph blue_b 6 := by
    apply ZeroForced.step 5 6 h5 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  have h7 : ZeroForced witness_graph blue_b 7 := by
    apply ZeroForced.step 6 7 h6 (by decide)
    intro v hv hne
    fin_cases v <;> simp_all [witness_graph, witness_edges]
  intro v
  fin_cases v <;> assumption

private theorem fort_blocking {V : Type*} (G : SimpleGraph V) (S F : Set V)
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

private theorem fort_blocks_complement {V : Type*} [Fintype V] [DecidableEq V]
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
  exact fort_blocking G ((Finset.univ \ W : Finset V) : Set V) (F : Set V) hdisj hf v (hS v) hv

private theorem forced_mono {V : Type*} (G : SimpleGraph V) {S T : Set V} (h : S ⊆ T) :
    ∀ v, ZeroForced G S v → ZeroForced G T v := by
  intro v hv
  induction hv with
  | init v hvS => exact ZeroForced.init v (h hvS)
  | step u w hu huw hothers ihu ihothers =>
    exact ZeroForced.step u w ihu huw ihothers

private def white_A : Finset (Fin 9) := {1, 4, 5, 7}
private def white_B : Finset (Fin 9) := {1, 2, 3, 4, 5, 6, 7}

private theorem blue_A_insert_forcing :
    is_zero_forcing_set witness_graph
      ((Finset.univ \ insert 8 white_A : Finset (Fin 9)) : Set (Fin 9)) := by
  have hset : ((Finset.univ \ insert 8 white_A : Finset (Fin 9)) : Set (Fin 9)) = blue_a := by
    ext v
    fin_cases v <;> simp [white_A, blue_a]
  rw [hset]
  exact blue_a_forcing

private theorem blue_B_forcing :
    is_zero_forcing_set witness_graph ((Finset.univ \ white_B : Finset (Fin 9)) : Set (Fin 9)) := by
  have hset : ((Finset.univ \ white_B : Finset (Fin 9)) : Set (Fin 9)) = blue_b := by
    ext v
    fin_cases v <;> simp [white_B, blue_b]
  rw [hset]
  exact blue_b_forcing

private theorem blue_A_forcing :
    is_zero_forcing_set witness_graph ((Finset.univ \ white_A : Finset (Fin 9)) : Set (Fin 9)) := by
  intro v
  apply forced_mono witness_graph (S := ((Finset.univ \ insert 8 white_A : Finset (Fin 9)) : Set (Fin 9)))
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxA => (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxA)⟩
  · exact blue_A_insert_forcing v

private theorem no_two_repairs (R : Finset (Fin 9)) (hR : R ⊆ white_B \ white_A)
    (hcard : R.card ≤ 2) :
    ¬ is_zero_forcing_set witness_graph
      ((Finset.univ \ insert 8 (white_B \ R) : Finset (Fin 9)) : Set (Fin 9)) := by
  have hBA : white_B \ white_A = ({2, 3, 6} : Finset (Fin 9)) := by decide
  have hsub : R ⊆ ({2, 3, 6} : Finset (Fin 9)) := by simpa only [hBA] using hR
  have h1 : (1 : Fin 9) ∉ R := by intro h; have hh := hsub h; simp at hh
  have h4 : (4 : Fin 9) ∉ R := by intro h; have hh := hsub h; simp at hh
  have h5 : (5 : Fin 9) ∉ R := by intro h; have hh := hsub h; simp at hh
  have h7 : (7 : Fin 9) ∉ R := by intro h; have hh := hsub h; simp at hh
  by_cases h2 : (2 : Fin 9) ∈ R <;> by_cases h3 : (3 : Fin 9) ∈ R <;> by_cases h6 : (6 : Fin 9) ∈ R
  · have hthree : ({2, 3, 6} : Finset (Fin 9)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hthree
    have hcard3 : ({2, 3, 6} : Finset (Fin 9)).card = 3 := by decide
    rw [hcard3] at hc
    omega
  · apply fort_blocks_complement witness_graph _ ({6, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 3, 4, 5, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 3, 4, 5, 6, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 2, 4, 5, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 2, 3, 4, 5, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide
  · apply fort_blocks_complement witness_graph _ ({1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9))
    · intro x hx
      fin_cases x <;> simp_all [white_B]
    · decide
    · decide

private theorem witness_not_two_extendible :
    ¬ (∀ A B : Finset (Fin 9), A ⊆ B →
      is_zero_forcing_set witness_graph ((Finset.univ \ A : Finset (Fin 9)) : Set (Fin 9)) →
      is_zero_forcing_set witness_graph ((Finset.univ \ B : Finset (Fin 9)) : Set (Fin 9)) →
      ∀ x : Fin 9, x ∉ B →
      is_zero_forcing_set witness_graph ((Finset.univ \ insert x A : Finset (Fin 9)) : Set (Fin 9)) →
      ∃ R : Finset (Fin 9), R ⊆ B \ A ∧ R.card ≤ 2 ∧
        is_zero_forcing_set witness_graph ((Finset.univ \ insert x (B \ R) : Finset (Fin 9)) : Set (Fin 9))) := by
  intro h
  have hab : white_A ⊆ white_B := by decide
  have hx : (8 : Fin 9) ∉ white_B := by decide
  obtain ⟨R, hR, hc, hforce⟩ := h white_A white_B hab blue_A_forcing blue_B_forcing 8 hx blue_A_insert_forcing
  exact no_two_repairs R hR hc hforce

theorem tree_zero_forcing_complements_not_two_extendible : ∃ G : SimpleGraph (Fin 9), G.IsTree ∧ ¬ zero_forcing_complements_two_extendible G := by
  exact ⟨witness_graph, witness_tree, witness_not_two_extendible⟩
