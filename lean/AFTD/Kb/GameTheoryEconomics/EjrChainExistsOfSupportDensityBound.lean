import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.EjrOfSupportDensityBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ejr_chain_exists_of_support_density_bound

Topic: social_choice   Node: 11a8f55bef07

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

A permutation whose every prefix satisfies the proposed density bound yields an EJR committee chain.
-/

theorem ejr_density_prefix_card_aux {m : ℕ} (σ : Equiv.Perm (Fin m))
    (k : ℕ) (hk : k ≤ m) :
    (Finset.univ.filter fun c => (σ c : ℕ) < k).card = k := by
  classical
  have he : (Finset.univ.filter fun c => (σ c : ℕ) < k).card =
      (Finset.univ.filter fun c : Fin m => (c : ℕ) < k).card := by
    apply Finset.card_bij (fun c _ => σ c)
    · intro c hc
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hc
    · intro a ha b hb hab
      exact σ.injective hab
    · intro b hb
      refine ⟨σ.symm b, ?_, by simp⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, σ.apply_symm_apply] using hb
  rw [he]
  by_cases hkm : k = m
  · subst k
    simp
  · have hlt : k < m := by omega
    have hI : (Finset.univ.filter fun c : Fin m => (c : ℕ) < k) =
        Finset.Iio (⟨k, hlt⟩ : Fin m) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rfl
    rw [hI, Fin.card_Iio]

theorem ejr_chain_exists_of_support_density_bound (n m : ℕ)
    (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (h : ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      ejr_support_density_bound A (k + 1)
        (Finset.univ.filter fun c => (σ c : ℕ) < k)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, fun k hk => ejr_of_support_density_bound A k _ hn
    (ejr_density_prefix_card_aux σ k hk) (hσ k hk)⟩
