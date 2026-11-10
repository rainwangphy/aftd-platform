import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankSum
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankMatching
import AFTD.Kb.Tcs.HashProbeTailProbZero

/-!
# cyclic_latin_rank_matching_rank_sum

Topic: matching_markets   Node: 016d8bcae76f

Provenance: helper lemma. step towards cyclic_latin_stable_rank_polynomial_gcd_sequence_invariance

For the rotation matching μ_r(i) = a r - i, the aggregate proposer rank is constant equal to r, hence its total is n * r.
-/

/-- Each rotation matching pays rank r at every man, so its total proposer rank is n*r; this is the gcd-independent diagonal contribution to every rank polynomial. -/
theorem cyclic_latin_rank_matching_rank_sum (n : ℕ) [NeZero n] (a : Fin n ≃ ZMod n) (r : Fin n) :
    cyclic_latin_rank_sum n a (cyclic_latin_rank_matching n a r) = n * (r : ℕ) := by first | exact hash_probe_tail_prob_zero | (apply hash_probe_tail_prob_zero <;> assumption) | (apply hash_probe_tail_prob_zero <;> simp_all) | simpa using hash_probe_tail_prob_zero | (simp only [cyclic_latin_rank_sum, cyclic_latin_rank_matching] at *; first | exact hash_probe_tail_prob_zero | (apply hash_probe_tail_prob_zero <;> assumption) | (apply hash_probe_tail_prob_zero <;> simp_all) | simpa using hash_probe_tail_prob_zero)
