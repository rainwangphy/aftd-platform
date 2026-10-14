import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming

/-!
# simple_graph_is_k_star_forming_iff

Topic: graphs   Node: 97033dd552ac

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Lemma 2.2.

For k ≥ 1, a vertex set S is k-star-forming if and only if every vertex v outside S has at least k neighbours in S, or has a neighbour u in S with at least k − 1 neighbours in S.
-/

theorem simple_graph_is_k_star_forming_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) (S : Finset V) :
    simple_graph_is_k_star_forming G k S ↔ ∀ v, v ∉ S →
      k ≤ (S.filter (G.Adj v)).card ∨ ∃ u ∈ S, G.Adj v u ∧ k - 1 ≤ (S.filter (G.Adj u)).card := open Finset in by
  constructor
  · intro h v hv
    obtain ⟨c, L, hc, hL, hcard, hadj, hvc⟩ := h v hv
    rcases hvc with rfl | hvL
    · left
      rw [← hcard]
      apply card_le_card
      intro x hx
      rw [mem_filter]
      rcases hL x hx with rfl | hxS
      · exact absurd (hadj _ hx) G.irrefl
      · exact ⟨hxS, hadj x hx⟩
    · right
      have hcv : c ≠ v := fun h => G.irrefl (by have := hadj v hvL; rwa [← h] at this)
      have hcS : c ∈ S := hc.resolve_left hcv
      refine ⟨c, hcS, (hadj v hvL).symm, ?_⟩
      have : (L.erase v).card = k - 1 := by rw [card_erase_of_mem hvL, hcard]
      rw [← this]
      apply card_le_card
      intro x hx
      rw [mem_erase] at hx
      rw [mem_filter]
      exact ⟨(hL x hx.2).resolve_left hx.1, hadj x hx.2⟩
  · intro h v hv
    rcases h v hv with h1 | ⟨u, huS, hvu, h2⟩
    · obtain ⟨L, hLs, hLc⟩ := exists_subset_card_eq h1
      refine ⟨v, L, Or.inl rfl, fun x hx => Or.inr (mem_filter.1 (hLs hx)).1, hLc,
        fun x hx => (mem_filter.1 (hLs hx)).2, Or.inl rfl⟩
    · obtain ⟨L, hLs, hLc⟩ := exists_subset_card_eq h2
      have hvL : v ∉ L := fun h => hv (mem_filter.1 (hLs h)).1
      refine ⟨u, insert v L, Or.inr huS, ?_, ?_, ?_, Or.inr (mem_insert_self v L)⟩
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (mem_filter.1 (hLs hx)).1
      · rw [card_insert_of_notMem hvL, hLc]
        omega
      · intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hvu.symm
        · exact (mem_filter.1 (hLs hx)).2
