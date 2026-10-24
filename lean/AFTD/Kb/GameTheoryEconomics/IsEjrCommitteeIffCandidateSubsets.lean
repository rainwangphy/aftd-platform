import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffUndersatisfiedSupporters
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# is_ejr_committee_iff_candidate_subsets

Topic: social_choice   Node: 1ed100158aaf

Provenance: helper lemma. Finite version of is_ejr_committee_iff_undersatisfied_supporters for OP-22 computational certificates: eliminate the unbounded demand quantifier by taking the demand to be the common candidate subset cardinality.

EJR is equivalent to the correct committee size together with the underrepresented-supporter inequality for every nonempty candidate subset T, with demand |T|. All remaining quantifiers range over finite types.
-/

theorem is_ejr_committee_iff_candidate_subsets {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) :
    is_ejr_committee A k W ↔ W.card = k ∧
      ∀ T : Finset (Fin m), T.Nonempty →
        (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < T.card).card * k < T.card * n := by
  classical
  rw [is_ejr_committee_iff_undersatisfied_supporters]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro T hT
    exact h T.card (by have := Finset.card_pos.mpr hT; omega) T rfl
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro ℓ hℓ T hT
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    simpa [hT] using h T hne
