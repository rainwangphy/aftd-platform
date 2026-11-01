import AFTD.Prelude
import AFTD.Kb.Tcs.MixedRadixOffset
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# mixed_radix_offset_prime

Topic: data_structures   Node: 4e896e0c1246

Provenance: helper lemma. arXiv:2610.31363

For any positive integer p and any index j in Fin p, the mixed-radix reversed offset with singleton factor list [p] equals the linear probing offset j in ZMod p.
-/

/-- For a prime size p, the mixed-radix reversed offset with singleton list [p] is linear probing. -/
theorem mixed_radix_offset_prime (p : ℕ) [NeZero p] (j : Fin p) :
    mixed_radix_offset p [p] j = linear_probe_offset p j := by
  simp [mixed_radix_offset, linear_probe_offset, Nat.div_self (NeZero.pos p)]
