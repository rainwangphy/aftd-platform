import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_chain_iff_level_supporters

Topic: social_choice   Node: 831b70c07d85

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

A permutation whose every prefix of length k is an EJR committee exists if and only if there is a permutation such that for every k ≤ m and every nonempty candidate subset T, the number of voters approving all of T who approve fewer than |T| candidates among the first k positions, times k, is strictly below |T| times the number of voters.
-/

private lemma ejr_chain_iff_level_supporters_card_prefix {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : ℕ)
    (hk : k ≤ m) : (Finset.univ.filter fun c => (σ c : ℕ) < k).card = k := by
  have hpre : (Finset.univ.filter fun c : Fin m => (σ c : ℕ) < k)
      = (Finset.univ.filter fun x : Fin m => (x : ℕ) < k).image σ.symm := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨σ c, h, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  have himg : (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)
      = Finset.univ.filter (fun x : Fin m => (x : ℕ) < k) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hx
      exact ⟨⟨x, hx⟩, Fin.ext rfl⟩
  rw [hpre, Finset.card_image_of_injective _ σ.symm.injective, ← himg,
    Finset.card_image_of_injective _ (Fin.castLE_injective hk), Finset.card_univ, Fintype.card_fin]

/-- The chain target is equivalent to a level-by-level counting condition on supporters of candidate subsets, with all cohesive-group machinery eliminated. -/
theorem ejr_chain_iff_level_supporters {n m : ℕ} (A : Fin n → Finset (Fin m)) :
    (∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
        is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k)) ↔
      (∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m → ∀ T : Finset (Fin m), T.Nonempty →
        (Finset.univ.filter fun i => T ⊆ A i ∧
          (A i ∩ Finset.univ.filter fun c => (σ c : ℕ) < k).card < T.card).card * k
        < T.card * n) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun k hk T hT =>
      ((is_ejr_committee_iff_candidate_subsets A k _).mp (hσ k hk)).2 T hT⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun k hk => ?_⟩
    rw [is_ejr_committee_iff_candidate_subsets]
    exact ⟨ejr_chain_iff_level_supporters_card_prefix σ k hk, fun T hT => hσ k hk T hT⟩
