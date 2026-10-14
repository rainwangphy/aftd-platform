import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumber
import AFTD.Kb.Tcs.SimpleGraphUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingUniv
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_k_independence_number_eq_card_of_degree_lt

Topic: graphs   Node: 4e3db2e76308

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Proposition 3.1.

If every vertex of the finite graph G has degree less than k, then β_k(G) = SF_k(G) = |V(G)|.
-/

theorem simple_graph_k_independence_number_eq_card_of_degree_lt {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v < k) :
    simple_graph_k_independence_number G k = Fintype.card V ∧
      simple_graph_upper_k_star_forming_number G k = Fintype.card V := open Finset in by
  have h_ind : simple_graph_is_k_independent G k Finset.univ := by
    intro v _
    have h_set : ({u | u ∈ (univ : Finset V) ∧ G.Adj v u} : Set V) = G.neighborSet v := by
      ext u
      simp
    rw [h_set, Set.ncard_eq_toFinset_card', ← G.neighborFinset_def]
    exact h v
  have h_sf_univ : simple_graph_is_k_star_forming G k Finset.univ :=
    fun v hv => absurd (Finset.mem_univ v) hv
  have h_not_sf : ∀ T ⊂ (univ : Finset V), ¬ simple_graph_is_k_star_forming G k T := by
    intro T hT hsf
    obtain ⟨s, -, hsT⟩ := Finset.exists_of_ssubset hT
    obtain ⟨c, L, -, -, hcard, hadj, -⟩ := hsf s hsT
    have h_sub : (L : Set V) ⊆ G.neighborSet c := by
      intro x hx
      exact hadj x (Finset.mem_coe.mp hx)
    have h_le := Set.ncard_le_ncard h_sub (Set.toFinite (G.neighborSet c))
    rw [Set.ncard_coe_finset, hcard, Set.ncard_eq_toFinset_card', ← G.neighborFinset_def] at h_le
    have h_lt := h c
    change (G.neighborFinset c).card < k at h_lt
    omega
  have h_min_sf : simple_graph_is_minimal_k_star_forming G k Finset.univ :=
    ⟨h_sf_univ, h_not_sf⟩
  constructor
  · dsimp [simple_graph_k_independence_number]
    apply le_antisymm
    · apply csSup_le
      · exact ⟨Fintype.card V, univ, h_ind, card_univ⟩
      · rintro n ⟨I, -, rfl⟩
        exact card_le_univ I
    · apply le_csSup
      · refine ⟨Fintype.card V, ?_⟩
        rintro n ⟨I, -, rfl⟩
        exact card_le_univ I
      · exact ⟨univ, h_ind, card_univ⟩
  · dsimp [simple_graph_upper_k_star_forming_number]
    apply le_antisymm
    · apply csSup_le
      · exact ⟨Fintype.card V, univ, h_min_sf, card_univ⟩
      · rintro n ⟨S, -, rfl⟩
        exact card_le_univ S
    · apply le_csSup
      · refine ⟨Fintype.card V, ?_⟩
        rintro n ⟨S, -, rfl⟩
        exact card_le_univ S
      · exact ⟨univ, h_min_sf, card_univ⟩
