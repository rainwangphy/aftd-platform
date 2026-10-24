import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.Tcs.V

/-!
# ejr_committee_nine_without_three_subset

Topic: social_choice   Node: 71620ba61369

Provenance: helper lemma. Helper counterexample for the fixed-core proof route to ejr_committee_monotone_chain_exists (OP-22; arXiv:2007.01795 Q2). Computations 4299 and 4310: three private candidate triples, each approved by a bloc of three voters, with two voters per bloc additionally approving a shared pair.

There is an approval profile with nine voters and eleven candidates and an EJR committee of size nine that contains no EJR committee of size three. This is an obstruction to building a whole monotone chain inside an arbitrary large EJR committee, not a refutation of monotone-chain existence.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem ejr_committee_nine_without_three_subset :
    ∃ (A : Fin 9 → Finset (Fin 11)) (W : Finset (Fin 11)),
      is_ejr_committee A 9 W ∧ ¬ ∃ V, V ⊆ W ∧ is_ejr_committee A 3 V := by
  let A : Fin 9 → Finset (Fin 11) := fun i =>
    let B := Finset.univ.filter fun c : Fin 11 => c.val < 9 ∧ c.val / 3 = i.val / 3
    if i.val % 3 < 2 then B ∪ {9, 10} else B
  let W : Finset (Fin 11) := Finset.univ.filter fun c => c.val < 9
  let under : Finset (Fin 11) → Finset (Fin 11) → ℕ := fun V T =>
    (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ V).card < T.card).card
  have hcore : is_ejr_committee A 9 W := by
    rw [is_ejr_committee_iff_candidate_subsets]
    set_option maxRecDepth 10000 in
    decide
  have cert : ∀ V : Finset (Fin 11), V ⊆ W → V.card = 3 →
      ¬ (under V {0} * 3 < 9 ∧ under V {3} * 3 < 9 ∧
         under V {6} * 3 < 9 ∧ under V {9, 10} * 3 < 18) := by
    set_option maxRecDepth 10000 in
    decide
  refine ⟨A, W, hcore, ?_⟩
  rintro ⟨V, hVW, hV⟩
  have h := (is_ejr_committee_iff_candidate_subsets A 3 V).mp hV
  have h0 := h.2 {0} (by decide)
  have h3 := h.2 {3} (by decide)
  have h6 := h.2 {6} (by decide)
  have h9 := h.2 {9, 10} (by decide)
  change under V {0} * 3 < 9 at h0
  change under V {3} * 3 < 9 at h3
  change under V {6} * 3 < 9 at h6
  change under V {9, 10} * 3 < 18 at h9
  exact cert V hVW h.1 ⟨h0, h3, h6, h9⟩
