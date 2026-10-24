import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_set_of_top_choices

Topic: social_choice   Node: 272f0d6dc091

Provenance: helper lemma. step towards condorcet_dimension_le_three

For any election with at least one candidate, the set of top-choice candidates of any subset of voters V0 is a Condorcet winning set provided that strictly fewer than n/2 voters lie outside V0.
-/

/-- The set of top-choice candidates of a voter subset V0 is a Condorcet winning set if strictly fewer than n/2 voters lie outside V0. -/
theorem condorcet_winning_set_of_top_choices {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (hm : 0 < m) (V0 : Finset (Fin n)) (hV0 : 2 * (n - V0.card) < n) :
    is_condorcet_winning_set P (V0.image fun v => (P v).symm ⟨0, hm⟩) := by
  intro a ha
  have hsub : (Finset.univ.filter fun v =>
      ∀ b ∈ V0.image (fun v => (P v).symm ⟨0, hm⟩), P v a < P v b)
      ⊆ Finset.univ \ V0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hvV
    have htop : (P v).symm ⟨0, hm⟩ ∈ V0.image (fun v => (P v).symm ⟨0, hm⟩) :=
      Finset.mem_image.mpr ⟨v, hvV, rfl⟩
    have hlt := hv _ htop
    have hzero : P v ((P v).symm ⟨0, hm⟩) = ⟨0, hm⟩ := Equiv.apply_symm_apply _ _
    rw [hzero] at hlt
    haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
    exact Fin.not_lt_zero (P v a) hlt
  have hcard : (Finset.univ.filter fun v =>
      ∀ b ∈ V0.image (fun v => (P v).symm ⟨0, hm⟩), P v a < P v b).card
      ≤ n - V0.card := by
    calc
      (Finset.univ.filter fun v =>
          ∀ b ∈ V0.image (fun v => (P v).symm ⟨0, hm⟩), P v a < P v b).card
          ≤ (Finset.univ \ V0).card := Finset.card_le_card hsub
      _ = n - V0.card := by
        rw [show Finset.univ \ V0 = V0ᶜ by ext; simp]
        rw [Finset.card_compl, Fintype.card_fin]
  omega
