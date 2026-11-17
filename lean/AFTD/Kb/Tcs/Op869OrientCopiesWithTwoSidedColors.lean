import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ManySharedColors
import AFTD.Kb.Tcs.Op869TwoSidedColorsByOrientation

/-!
# op869_orient_copies_with_two_sided_colors

Topic: online_algorithms   Node: 383429bb5572

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.4

If each of K copies has at least 2q designated-side colors and fewer than K colors occur, orient the copies so that at least q colors occur on both overall sides.
-/

/-- A finite combinatorial step in the three-colorable online-coloring simulation. -/
theorem op869_orient_copies_with_two_sided_colors {β : Type} [DecidableEq β]
    (K q : ℕ) (B : Finset β) (R : Fin K → β → Prop) [DecidableRel R]
    (hB : B.card < K) (hd : ∀ a, 2*q ≤ (B.filter (R a)).card) :
    ∃ s : Finset (Fin K), q ≤ (B.filter (fun c =>
      (∃ a : Fin K, a ∈ s ∧ R a c) ∧ (∃ b : Fin K, b ∉ s ∧ R b c))).card := by
  classical
  let A : Finset (Fin K) := Finset.univ
  let E : Fin K → Finset β := fun a => B.filter (R a)
  let H : Finset β := B.filter (fun c => 2 ≤ (A.filter (fun a => c ∈ E a)).card)
  have hshared : 2*q ≤ H.card := by
    apply op869_many_shared_colors A B E (2*q)
    · intro a ha b hb
      exact (Finset.mem_filter.mp hb).1
    · intro a ha
      exact hd a
    · simpa [A] using hB
  have hex : ∀ c ∈ H, ∃ a b : Fin K, a ≠ b ∧ R a c ∧ R b c := by
    intro c hc
    have hcount := (Finset.mem_filter.mp hc).2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (A.filter (fun a => c ∈ E a)).card)
    have hca := (Finset.mem_filter.mp ha).2
    have hcb := (Finset.mem_filter.mp hb).2
    exact ⟨a, b, hab, (Finset.mem_filter.mp hca).2, (Finset.mem_filter.mp hcb).2⟩
  obtain ⟨s, hs⟩ := op869_two_sided_colors_by_orientation K H R hex
  refine ⟨s, ?_⟩
  have hsubset : H.filter (fun c => (∃ a : Fin K, a ∈ s ∧ R a c) ∧ (∃ b : Fin K, b ∉ s ∧ R b c)) ⊆
      B.filter (fun c => (∃ a : Fin K, a ∈ s ∧ R a c) ∧ (∃ b : Fin K, b ∉ s ∧ R b c)) := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1, (Finset.mem_filter.mp hc).2⟩
  have hle := Finset.card_le_card hsubset
  omega
