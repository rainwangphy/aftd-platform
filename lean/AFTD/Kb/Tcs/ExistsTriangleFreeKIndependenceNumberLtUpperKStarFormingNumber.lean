import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumber
import AFTD.Kb.Tcs.SimpleGraphUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingMono
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentIff
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingIff
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentMono
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# exists_triangle_free_k_independence_number_lt_upper_k_star_forming_number

Topic: graphs   Node: 4ac1274b2895

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Proposition 7.1 (the explicit graph with edges 02, 08, 09, 01, 13, 15, 14, 16, 24, 25, 26, 37, 47, 57, 67, 78).

There is a triangle-free graph H on 10 vertices with β_4(H) = 7 < 8 = SF_4(H).
-/

def star_forming_example_edges : List (ℕ × ℕ) :=
  [(0,2),(0,8),(0,9),(0,1),(1,3),(1,5),(1,4),(1,6),(2,4),(2,5),(2,6),(3,7),(4,7),(5,7),(6,7),(7,8)]

def star_forming_example_graph : SimpleGraph (Fin 10) where
  Adj i j := (i.val, j.val) ∈ star_forming_example_edges ∨ (j.val, i.val) ∈ star_forming_example_edges
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by decide⟩

instance : DecidableRel star_forming_example_graph.Adj := fun i j => by
  unfold star_forming_example_graph
  infer_instance

theorem exists_triangle_free_k_independence_number_lt_upper_k_star_forming_number :
    ∃ H : SimpleGraph (Fin 10), H.CliqueFree 3 ∧
      simple_graph_k_independence_number H 4 = 7 ∧
      simple_graph_upper_k_star_forming_number H 4 = 8 := open Finset in by
  set H := star_forming_example_graph with hH
  unfold simple_graph_k_independence_number simple_graph_upper_k_star_forming_number
  refine ⟨H, ?_, ?_, ?_⟩
  · intro s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
    have key : ∀ a b c : Fin 10, H.Adj a b → H.Adj a c → H.Adj b c → False := by
      decide
    exact key a b c hab hac hbc
  · -- β_4(H) = 7
    have hbdd : BddAbove {n | ∃ I : Finset (Fin 10), simple_graph_is_k_independent H 4 I ∧
        I.card = n} := ⟨10, fun n ⟨I, _, hn⟩ => hn ▸ (card_le_univ I).trans (by simp)⟩
    apply le_antisymm
    · refine csSup_le (Set.nonempty_of_mem (x := 0) ⟨∅, fun v hv => by simp at hv, rfl⟩) ?_
      rintro n ⟨I, hI, rfl⟩
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJI, hJc⟩ := exists_subset_card_eq (show 8 ≤ I.card by omega)
      have hJ := simple_graph_is_k_independent_mono H 4 hJI hI
      rw [simple_graph_is_k_independent_iff] at hJ
      have hc : (univ \ J).card = 2 := by
        rw [card_sdiff_of_subset (subset_univ J), card_univ, Fintype.card_fin, hJc]
      obtain ⟨x, y, hxy, hxyJ⟩ := card_eq_two.1 hc
      have hJeq : J = univ.filter (fun u => u ≠ x ∧ u ≠ y) := by
        ext u
        have := congrArg (u ∈ ·) hxyJ
        simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, eq_iff_iff] at this
        simp only [mem_filter, mem_univ, true_and]
        tauto
      rw [hJeq] at hJ
      have key : ∀ x y : Fin 10, x ≠ y → ∃ v, v ≠ x ∧ v ≠ y ∧
          4 ≤ ((univ.filter (fun u => u ≠ x ∧ u ≠ y)).filter (H.Adj v)).card := by
        decide
      obtain ⟨v, hvx, hvy, hv⟩ := key x y hxy
      have := hJ v (by simp [hvx, hvy])
      omega
    · apply le_csSup hbdd
      refine ⟨{0, 1, 2, 3, 4, 7, 8}, ?_, rfl⟩
      rw [simple_graph_is_k_independent_iff]
      decide
  · -- SF_4(H) = 8
    have hloc := simple_graph_is_k_star_forming_iff H 4 (by norm_num)
    have hbdd : BddAbove {n | ∃ S : Finset (Fin 10),
        simple_graph_is_minimal_k_star_forming H 4 S ∧ S.card = n} :=
      ⟨10, fun n ⟨S, _, hn⟩ => hn ▸ (card_le_univ S).trans (by simp)⟩
    have hmem : 8 ∈ {n | ∃ S : Finset (Fin 10),
        simple_graph_is_minimal_k_star_forming H 4 S ∧ S.card = n} := by
      refine ⟨{0, 1, 2, 3, 4, 5, 6, 9}, ⟨?_, ?_⟩, rfl⟩
      · rw [hloc]
        decide
      · intro T hT hTsf
        obtain ⟨s, hsS, hsT⟩ := exists_of_ssubset hT
        have hsub : T ⊆ ({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)).erase s := by
          intro x hx
          rw [mem_erase]
          exact ⟨fun h => hsT (h ▸ hx), hT.1 hx⟩
        have h2 := simple_graph_is_k_star_forming_mono H 4 hsub hTsf
        rw [hloc] at h2
        have key : ∀ s ∈ ({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)), ¬ ∀ v,
            v ∉ ({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)).erase s →
            4 ≤ ((({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)).erase s).filter (H.Adj v)).card ∨
              ∃ u ∈ ({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)).erase s, H.Adj v u ∧
                4 - 1 ≤ ((({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 10)).erase s).filter
                  (H.Adj u)).card := by
          decide
        exact key s hsS h2
    apply le_antisymm
    · refine csSup_le ⟨8, hmem⟩ ?_
      rintro n ⟨S, ⟨hS, hmin⟩, rfl⟩
      by_contra hlt
      push_neg at hlt
      have hc : (univ \ S).card ≤ 1 := by
        rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
        omega
      -- some vertex `r ∈ S` can be removed
      have key1 : ∃ r : Fin 10, ∀ v, v ∉ univ.erase r →
          4 ≤ ((univ.erase r).filter (H.Adj v)).card ∨
            ∃ u ∈ univ.erase r, H.Adj v u ∧ 4 - 1 ≤ ((univ.erase r).filter (H.Adj u)).card := by
        decide
      have key2 : ∀ x : Fin 10, ∃ r, r ≠ x ∧ ∀ v, v ∉ ((univ.erase x).erase r) →
          4 ≤ (((univ.erase x).erase r).filter (H.Adj v)).card ∨
            ∃ u ∈ ((univ.erase x).erase r), H.Adj v u ∧
              4 - 1 ≤ ((((univ.erase x).erase r)).filter (H.Adj u)).card := by
        decide
      rcases card_le_one_iff_subset_singleton.1 hc with ⟨x, hx⟩
      by_cases hxS : x ∈ S
      · have hSu : S = univ := by
          ext u
          simp only [mem_univ, iff_true]
          by_contra hu
          have : u ∈ univ \ S := by simp [hu]
          have := hx this
          rw [mem_singleton] at this
          exact hu (this ▸ hxS)
        obtain ⟨r, hr⟩ := key1
        exact hmin (univ.erase r) (by rw [hSu]; exact erase_ssubset (mem_univ r)) ((hloc _).2 hr)
      · have hSu : S = univ.erase x := by
          ext u
          simp only [mem_erase, mem_univ, and_true]
          constructor
          · intro hu h
            exact hxS (h ▸ hu)
          · intro hu
            by_contra hu'
            have : u ∈ univ \ S := by simp [hu']
            exact hu (mem_singleton.1 (hx this))
        obtain ⟨r, hrx, hr⟩ := key2 x
        exact hmin ((univ.erase x).erase r)
          (by rw [hSu]; exact erase_ssubset (mem_erase.2 ⟨hrx, mem_univ r⟩)) ((hloc _).2 hr)
    · exact le_csSup hbdd hmem
