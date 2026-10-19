import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingKendallTau

/-!
# ranking_kendall_tau_le

Topic: fair_division   Node: 7d3354ad850e

Provenance: helper lemma. Helper for iterated_round_robin_two_agents_item_preserving_swaps_le (arXiv:2610.23040 Theorem 3.12): the initial distance is at most m(m-1)/2.

The Kendall tau distance between two rankings of m goods is at most m(m-1)/2.
-/

theorem ranking_kendall_tau_le {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ} (r s : Fin m ≃ G) :
    ranking_kendall_tau r s ≤ m * (m - 1) / 2 := by
  have h1 : ranking_kendall_tau r s ≤
      ((Finset.univ : Finset (Fin m × Fin m)).filter (fun x => x.1 < x.2)).card := by
    dsimp [ranking_kendall_tau]
    apply Finset.card_le_card_of_injOn (fun p => (r.symm p.1, r.symm p.2))
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, hp.2.1⟩
    · intro p1 _ p2 _ h
      have h' : (r.symm p1.1, r.symm p1.2) = (r.symm p2.1, r.symm p2.2) := h
      injection h' with h1 h2
      exact Prod.ext (r.symm.injective h1) (r.symm.injective h2)
  have h2 : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun x => x.1 < x.2)).card =
      (Fintype.card (Fin m)).choose 2 :=
    Fintype.card_product_filter_lt
  rw [Fintype.card_fin, Nat.choose_two_right] at h2
  omega
