import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatInc
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent

/-!
# higher_bruhat_inc_le

Topic: combinatorics   Node: 4598c9c54b53

Provenance: formalization of a published result. Source: arXiv:2611.17465 Definition 1

The partial order relation on the inclusion higher Bruhat order B_inc(n, k) is given by inclusion of families: X ≤ Y if and only if X ⊆ Y.
-/

/-- The inclusion order relation on B_inc(n, k). -/
def higher_bruhat_inc_le (n k : ℕ) (X Y : higher_bruhat_inc n k) : Prop :=
  X.1 ⊆ Y.1
