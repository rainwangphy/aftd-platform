import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber

/-!
# is_m_number_of_dvd_not_dvd_pow

Topic: elementary_number_theory   Node: 6b52da3b80f7

Provenance: helper lemma. arXiv:2610.37512, Section 6, proof of Corollary 1.4

For natural numbers d, n, and p, if d divides n, every prime q such that q^q divides n satisfies q = p, and p^p does not divide d, then d is an M-number.
-/

/-- If all prime powers q^q dividing n have q = p, and p^p does not divide d for a divisor d of n, then d is an M-number. -/
theorem is_m_number_of_dvd_not_dvd_pow {d n p : ℕ} (hdn : d ∣ n)
    (h_uniq : ∀ q : ℕ, q.Prime → q ^ q ∣ n → q = p)
    (h_not : ¬ p ^ p ∣ d) :
    is_m_number d := by
  intro q hq hq_pow
  have hqn : q ^ q ∣ n := dvd_trans hq_pow hdn
  have heq : q = p := h_uniq q hq hqn
  subst heq
  exact h_not hq_pow
