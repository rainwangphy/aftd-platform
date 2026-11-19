import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctTriples

/-!
# distinct_triples_card

Topic: information   Node: afa827c1cf7f

Provenance: formalization of a published result. Source: arXiv:2611.21275, Section II

For any finite set s, the cardinality of the set of ordered triples of pairwise distinct elements in s is equal to s.card * (s.card - 1) * (s.card - 2).
-/

/-- The number of ordered triples of pairwise distinct elements in a finite set s is |s|(|s| - 1)(|s| - 2). -/
theorem distinct_triples_card {α : Type*} [DecidableEq α] (s : Finset α) : (distinct_triples s).card = s.card * (s.card - 1) * (s.card - 2) := by
  have H : (distinct_triples s : Set (α × α × α)).MapsTo (fun x => x.1) s := by
    intro x hx
    dsimp [distinct_triples] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx
    exact hx.1.1
  rw [Finset.card_eq_sum_card_fiberwise H]
  have h_fib : ∀ a ∈ s, ({x ∈ distinct_triples s | x.1 = a} : Finset (α × α × α)).card = (s.card - 1) * (s.card - 2) := by
    intro a ha
    have h_card : ({x ∈ distinct_triples s | x.1 = a} : Finset (α × α × α)).card = (s.erase a).offDiag.card := by
      refine Finset.card_bij' (fun x _ => x.2) (fun bc _ => (a, bc)) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter] at hx
        rcases hx with ⟨hx1, rfl⟩
        dsimp [distinct_triples] at hx1
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hx1
        rcases hx1 with ⟨⟨ha', hb, hc⟩, hab, hac, hbc⟩
        rw [Finset.mem_offDiag, Finset.mem_erase, Finset.mem_erase]
        exact ⟨⟨Ne.symm hab, hb⟩, ⟨Ne.symm hac, hc⟩, hbc⟩
      · intro bc hbc
        rw [Finset.mem_offDiag, Finset.mem_erase, Finset.mem_erase] at hbc
        rcases hbc with ⟨⟨hab, hb⟩, ⟨hac, hc⟩, hbc⟩
        rw [Finset.mem_filter]
        refine ⟨?_, rfl⟩
        dsimp [distinct_triples]
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨ha, hb, hc⟩, Ne.symm hab, Ne.symm hac, hbc⟩
      · intro x hx
        rw [Finset.mem_filter] at hx
        exact Prod.ext hx.2.symm rfl
      · intro bc _
        rfl
    rw [h_card, Finset.offDiag_card, Finset.card_erase_of_mem ha]
    rcases s.card with _ | _ | n
    · rfl
    · rfl
    · change (n + 1) * (n + 1) - (n + 1) = (n + 1) * n
      rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [Finset.sum_const_nat h_fib, mul_assoc]
