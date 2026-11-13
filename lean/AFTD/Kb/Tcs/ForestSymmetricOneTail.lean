import AFTD.Prelude
import AFTD.Kb.Tcs.ForestSymmetricFiberEquiv

/-!
# forest_symmetric_one_tail

Topic: online_algorithms   Node: d113195fe084

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For any nonempty finite uniform symmetric integer law, the probability of being at least one is at most one half.
-/

theorem forest_symmetric_one_tail (α : Type) [Fintype α] [Nonempty α] (X : α → ℤ)
    (hs : ∀ z : ℤ, (Finset.univ.filter (fun a => X a = z)).card =
      (Finset.univ.filter (fun a => X a = -z)).card) :
    (((Finset.univ.filter (fun a => (1 : ℤ) ≤ X a)).card : ℝ) /
      (Fintype.card α : ℝ)) ≤ 1 / 2 := by
  classical
  obtain ⟨e, he⟩ := forest_symmetric_fiber_equiv α X hs
  let pos : Finset α := Finset.univ.filter (fun a => 1 ≤ X a)
  let neg : Finset α := Finset.univ.filter (fun a => X a ≤ -1)
  have heq : pos.card = neg.card := by
    let ep : {a // 1 ≤ X a} ≃ {a // X a ≤ -1} := e.subtypeEquiv (by
      intro a
      rw [he]
      omega)
    simpa only [Fintype.card_subtype] using Fintype.card_congr ep
  have hd : Disjoint pos neg := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h1 : 1 ≤ X a := (Finset.mem_filter.mp ha).2
    have h2 : X a ≤ -1 := (Finset.mem_filter.mp hb).2
    omega
  have hsum : pos.card + neg.card ≤ Fintype.card α := by
    calc
      _ = (pos ∪ neg).card := (Finset.card_union_of_disjoint hd).symm
      _ ≤ (Finset.univ : Finset α).card := Finset.card_le_card (Finset.subset_univ _)
      _ = _ := Finset.card_univ
  have htwo : 2 * pos.card ≤ Fintype.card α := by omega
  have hr : (2 : ℝ) * pos.card ≤ Fintype.card α := by exact_mod_cast htwo
  have hp : (0 : ℝ) < Fintype.card α := by exact_mod_cast (Fintype.card_pos (α := α))
  change (pos.card : ℝ) / (Fintype.card α : ℝ) ≤ 1 / 2
  apply (div_le_iff₀ hp).2
  nlinarith
