import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# ejr_committee_exists

Topic: social_choice   Node: f9ba496b77ed

Provenance: formalization of a published result. Source: Justified Representation in Approval-Based Committee Voting (arXiv:1407.8269), theorem that PAV satisfies EJR; recalled in arXiv:2007.01795; the one-size-at-a-time part of the committee-monotonicity question

For every approval profile with at least one voter and every committee size k ≤ m, some committee of size k satisfies EJR (for instance the PAV committee).
-/

/-- The greedy cohesive argument: for every set `S` of voters there is a set `W` of at most
`|S| k / n` candidates such that every `ℓ`-cohesive group inside `S` has a member approving at
least `ℓ` members of `W`. (Take a cohesive group `G ⊆ S` with the largest `ℓ`, give it `ℓ`
commonly approved candidates and recurse on `S \ G`.) -/
theorem ejr_greedy_cohesive_aux {n m : ℕ} (A : Fin n → Finset (Fin m)) (k : ℕ) (hn : 0 < n)
    (S : Finset (Fin n)) : ∃ W : Finset (Fin m), W.card * n ≤ S.card * k ∧
      ∀ ℓ, 1 ≤ ℓ → ∀ G ⊆ S, is_ejr_cohesive_group A k ℓ G → ∃ i ∈ G, ℓ ≤ (A i ∩ W).card := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  have hle_m : ∀ ℓ G, is_ejr_cohesive_group A k ℓ G → ℓ ≤ m := fun ℓ G h =>
    h.2.trans ((Finset.card_le_univ _).trans (by simp))
  let P : Finset (ℕ × Finset (Fin n)) :=
    ((Finset.Icc 1 m) ×ˢ S.powerset).filter fun p => is_ejr_cohesive_group A k p.1 p.2
  have hmemP : ∀ ℓ G, (ℓ, G) ∈ P ↔ (1 ≤ ℓ ∧ G ⊆ S ∧ is_ejr_cohesive_group A k ℓ G) := by
    intro ℓ G
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, hle_m ℓ G h3⟩, h2⟩, h3⟩
  by_cases hP : P.Nonempty
  · obtain ⟨⟨ℓ, G⟩, hpP, hmax⟩ := P.exists_max_image Prod.fst hP
    obtain ⟨hℓ1, hGS, hcoh⟩ := (hmemP ℓ G).1 hpP
    have hGne : G.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      have h := hcoh.1
      simp only [Finset.card_empty, zero_mul] at h
      have : 0 < ℓ * n := Nat.mul_pos hℓ1 hn
      omega
    obtain ⟨W', hW'card, hW'⟩ := ih (S \ G) (Finset.sdiff_ssubset hGS hGne)
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hcoh.2
    refine ⟨W' ∪ C, ?_, ?_⟩
    · have h1 : (W' ∪ C).card ≤ W'.card + ℓ := (Finset.card_union_le _ _).trans (by rw [hCcard])
      have h2 : (S \ G).card + G.card = S.card := Finset.card_sdiff_add_card_eq_card hGS
      have hc := hcoh.1
      calc (W' ∪ C).card * n ≤ (W'.card + ℓ) * n := Nat.mul_le_mul_right _ h1
        _ = W'.card * n + ℓ * n := by ring
        _ ≤ (S \ G).card * k + G.card * k := Nat.add_le_add hW'card hc
        _ = S.card * k := by rw [← Nat.add_mul, h2]
    · intro ℓ' hℓ' H hHS hHcoh
      by_cases hHG : Disjoint H G
      · have hHsub : H ⊆ S \ G := fun x hx =>
          Finset.mem_sdiff.2 ⟨hHS hx, Finset.disjoint_left.1 hHG hx⟩
        obtain ⟨i, hi, hle⟩ := hW' ℓ' hℓ' H hHsub hHcoh
        exact ⟨i, hi, hle.trans (Finset.card_le_card
          (Finset.inter_subset_inter_left Finset.subset_union_left))⟩
      · obtain ⟨i, hiH, hiG⟩ := Finset.not_disjoint_iff.1 hHG
        have hℓ'le : ℓ' ≤ ℓ := hmax (ℓ', H) ((hmemP ℓ' H).2 ⟨hℓ', hHS, hHcoh⟩)
        refine ⟨i, hiH, hℓ'le.trans ?_⟩
        rw [← hCcard]
        apply Finset.card_le_card
        intro c hc
        exact Finset.mem_inter.2 ⟨(Finset.mem_filter.1 (hCsub hc)).2 i hiG,
          Finset.mem_union_right _ hc⟩
  · refine ⟨∅, by simp, ?_⟩
    intro ℓ hℓ G hGS hcoh
    exact absurd ⟨(ℓ, G), (hmemP ℓ G).2 ⟨hℓ, hGS, hcoh⟩⟩ hP

theorem ejr_committee_exists :
    ∀ (n m : ℕ) (A : Fin n → Finset (Fin m)), 0 < n → ∀ k, k ≤ m →
      ∃ W, is_ejr_committee A k W := by
  intro n m A hn k hk
  classical
  obtain ⟨W, hWc, hW⟩ := ejr_greedy_cohesive_aux A k hn Finset.univ
  have hWk : W.card ≤ k := by
    rw [Finset.card_univ, Fintype.card_fin] at hWc
    exact Nat.le_of_mul_le_mul_right (by rw [mul_comm k n]; exact hWc) hn
  obtain ⟨W2, hsub, hcard⟩ := Finset.exists_superset_card_eq hWk (by simpa using hk)
  refine ⟨W2, hcard, fun ℓ hℓ G hG => ?_⟩
  obtain ⟨i, hi, hle⟩ := hW ℓ hℓ G (Finset.subset_univ _) hG
  exact ⟨i, hi, hle.trans (Finset.card_le_card (Finset.inter_subset_inter_left hsub))⟩
