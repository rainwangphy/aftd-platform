import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_apex_over_bidirected_complete_min_cut_le

Topic: graphs   Node: d79b86ea662f

Provenance: helper lemma. Lemma for digraph_min_cut_additive_bound_fails_for_every_d; arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 6.

For every vertex set A of D_d, min(e(A, Aᶜ), e(Aᶜ, A)) ≤ ⌊(d + 1)²/4⌋.
-/

theorem digraph_apex_over_bidirected_complete_min_cut_le (d : ℕ)
    [DecidableRel (digraph_apex_over_bidirected_complete d).Adj] (A : Finset (Fin (d + 2))) :
    min (digraph_cut_count (digraph_apex_over_bidirected_complete d) A Aᶜ)
        (digraph_cut_count (digraph_apex_over_bidirected_complete d) Aᶜ A) ≤ (d + 1) ^ 2 / 4 := by
  have hab : ∀ a b : ℕ, a + b = d + 1 → a * b ≤ (d + 1) ^ 2 / 4 := by
    intro a b hab
    rw [Nat.le_div_iff_mul_le (by norm_num), ← hab]
    zify
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  have hA : A.card ≤ d + 2 := by simpa using A.card_le_univ
  by_cases hz : Fin.last (d + 1) ∈ A
  · have h1 : (Aᶜ ×ˢ A).filter (fun p => (digraph_apex_over_bidirected_complete d).Adj p.1 p.2) =
        Aᶜ ×ˢ A.erase (Fin.last (d + 1)) := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl, Finset.mem_erase]
      change ((_ ∧ _) ∧ (u ≠ v ∧ v ≠ Fin.last (d + 1))) ↔ _
      constructor
      · rintro ⟨⟨hu, hv⟩, -, hvz⟩
        exact ⟨hu, hvz, hv⟩
      · rintro ⟨hu, hvz, hv⟩
        exact ⟨⟨hu, hv⟩, fun h => hu (h ▸ hv), hvz⟩
    refine (min_le_right _ _).trans ?_
    unfold digraph_cut_count
    rw [h1, Finset.card_product]
    apply hab
    rw [Finset.card_erase_of_mem hz, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_pos.2 ⟨_, hz⟩
    omega
  · have h1 : (A ×ˢ Aᶜ).filter (fun p => (digraph_apex_over_bidirected_complete d).Adj p.1 p.2) =
        A ×ˢ Aᶜ.erase (Fin.last (d + 1)) := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl, Finset.mem_erase]
      change ((_ ∧ _) ∧ (u ≠ v ∧ v ≠ Fin.last (d + 1))) ↔ _
      constructor
      · rintro ⟨⟨hu, hv⟩, -, hvz⟩
        exact ⟨hu, hvz, hv⟩
      · rintro ⟨hu, hvz, hv⟩
        exact ⟨⟨hu, hv⟩, fun h => hv (h ▸ hu), hvz⟩
    refine (min_le_left _ _).trans ?_
    unfold digraph_cut_count
    rw [h1, Finset.card_product]
    apply hab
    have hz' : Fin.last (d + 1) ∈ Aᶜ := Finset.mem_compl.2 hz
    rw [Finset.card_erase_of_mem hz', Finset.card_compl, Fintype.card_fin]
    have : A.card ≤ d + 1 := by
      simpa using Finset.card_lt_univ_of_notMem hz
    omega
