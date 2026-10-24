import AFTD.Prelude
import AFTD.Kb.Tcs.PrefixReversal

/-!
# prefixReversal_involutive

Topic: combinatorics   Node: ac9db6dba8b7

Provenance: helper lemma. arXiv:2610.30892 Section 1

Applying a prefix reversal of length k twice in Equiv.Perm (Fin n) yields the identity permutation.
-/

/-- Every prefix reversal permutation is an involution. -/
theorem prefixReversal_involutive (n k : ℕ) :
    prefixReversal n k * prefixReversal n k = 1 := Equiv.ext (prefixReversal n k).left_inv
