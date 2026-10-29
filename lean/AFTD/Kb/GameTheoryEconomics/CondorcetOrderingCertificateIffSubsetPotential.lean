import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingScoreLeSubsetPotential
import AFTD.Kb.GameTheoryEconomics.CondorcetSubsetPotentialOfOrderingBound

/-!
# condorcet_ordering_certificate_iff_subset_potential

Topic: social_choice   Node: 60a20a2c0a45

Provenance: helper lemma. IN-339 verification route for OP-19, extending the uniform ordering-certificate reduction and the exact strict-majority convention in Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015). Related selector formulation arXiv:2604.19851v2. This is a certificate equivalence, not a new winning-set bound or research advance.

For any finite family of challenger claims and fixed nonnegative integer claim weights, a strict half-weight score bound for every strict ranking is equivalent to the existence of a natural-valued remaining-subset potential satisfying all local first-candidate removal inequalities and the same strict half-weight full-set bound. Unrestricted potentials add no loss to the ordering-certificate method; bounding their degree is an extra restriction.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

theorem condorcet_ordering_certificate_iff_subset_potential
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) :
    (∀ σ : Equiv.Perm (Fin m),
      2 * (∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) < ∑ i, w i) ↔
    ∃ H : Finset (Fin m) → ℕ,
      (∀ A : Finset (Fin m), ∀ a ∈ A,
        (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
      2 * H univ < ∑ i, w i := by
  classical
  constructor
  · intro hcert
    let score : Equiv.Perm (Fin m) → ℕ := fun σ =>
      ∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0
    let M : ℕ := univ.sup score
    have hM : ∀ σ, score σ ≤ M := fun σ => Finset.le_sup (mem_univ σ)
    have hne : (univ : Finset (Equiv.Perm (Fin m))).Nonempty := ⟨1, mem_univ _⟩
    obtain ⟨σ, _, heq⟩ := Finset.sup_mem_of_nonempty (s := univ) (f := score) hne
    have hstrict : 2 * M < ∑ i, w i := by
      change 2 * (univ.sup score) < _
      rw [← heq]
      exact hcert σ
    obtain ⟨H, hstep, hfull⟩ := condorcet_subset_potential_of_ordering_bound m q S f w M hM
    exact ⟨H, hstep, lt_of_le_of_lt (Nat.mul_le_mul_left 2 hfull) hstrict⟩
  · rintro ⟨H, hstep, hstrict⟩ σ
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2
      (condorcet_ordering_score_le_subset_potential m q S f w H hstep σ)) hstrict
