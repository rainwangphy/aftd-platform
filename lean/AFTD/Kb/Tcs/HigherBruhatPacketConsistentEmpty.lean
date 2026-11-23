import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# higher_bruhat_packet_consistent_empty

Topic: combinatorics   Node: 73f5bb610b09

Provenance: helper lemma. folklore

The empty family of subsets of {0, ..., n-1} is packet-consistent for any n and k.
-/

/-- The empty family is packet-consistent. -/
theorem higher_bruhat_packet_consistent_empty (n k : ℕ) :
    higher_bruhat_packet_consistent n k ∅ := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [higher_bruhat_packet_consistent] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
