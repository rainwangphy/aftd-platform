import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_near_regular_of_card_degrees

Topic: graphs   Node: 3b0a4c211570

Provenance: original. Related work: arXiv:2610.25886

If a digraph on 2m vertices has exactly m vertices of out-degree m - 1 and exactly m vertices of out-degree m, then it is near-regular.
-/

/-- A digraph on 2m vertices with m vertices of out-degree m - 1 and m vertices of out-degree m is near-regular. -/
theorem tournament_near_regular_of_card_degrees (m : ℕ)
    (T : Digraph (Fin (2 * m))) [DecidableRel T.Adj]
    (hdeg : (Finset.univ.filter (fun v => digraph_out_count T v = m - 1)).card = m ∧
            (Finset.univ.filter (fun v => digraph_out_count T v = m)).card = m) :
    tournament_is_near_regular m T := by
  intro v
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Fin.elim0 v
  · open Finset in
    let A := univ.filter (fun v => digraph_out_count T v = m - 1)
    let B := univ.filter (fun v => digraph_out_count T v = m)
    have hdisj : Disjoint A B := by
      rw [disjoint_filter]
      intro x _ h1 h2
      have : m - 1 ≠ m := by omega
      exact this (h1.symm.trans h2)
    have hcard : (A ∪ B).card = 2 * m := by
      rw [card_union_of_disjoint hdisj, hdeg.1, hdeg.2]
      omega
    have huniv : A ∪ B = univ := by
      apply eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    have hv : v ∈ A ∪ B := by
      rw [huniv]
      exact mem_univ v
    rw [mem_union, mem_filter, mem_filter] at hv
    rcases hv with ⟨-, h1⟩ | ⟨-, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
