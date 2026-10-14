import AFTD.Prelude
import AFTD.Kb.NumberTheory.NatLeastPrimeNotDvd

/-!
# nat_least_prime_not_dvd_two

Topic: elementary_number_theory   Node: 4616a088d9f8

Provenance: helper lemma. Sanity lemma for q(m), arXiv:2610.16562 (The Davenport constant of low-dimensional boxes).

The smallest prime not dividing 2 is 3.
-/

theorem nat_least_prime_not_dvd_two : nat_least_prime_not_dvd 2 = 3 := by
  unfold nat_least_prime_not_dvd
  apply le_antisymm
  · exact Nat.sInf_le (show 3 ∈ {p | p.Prime ∧ ¬ p ∣ 2} from ⟨Nat.prime_three, by norm_num⟩)
  · apply le_csInf (show ({p | p.Prime ∧ ¬ p ∣ 2} : Set ℕ).Nonempty from ⟨3, Nat.prime_three, by norm_num⟩)
    rintro p ⟨hp, hpd⟩
    by_contra h
    push_neg at h
    interval_cases p
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp
    · exact hpd (dvd_refl 2)
