import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent

/-!
# higher_bruhat_inc

Topic: combinatorics   Node: 5c11c193e39c

Provenance: formalization of a published result. Source: arXiv:2611.17465 Definition 1

The inclusion higher Bruhat order type B_inc(n, k) is the subtype of families X of subsets of {0, ..., n-1} such that each element of X has cardinality k+1 and X is packet-consistent.
-/

/-- The inclusion higher Bruhat poset B_inc(n, k), whose elements are consistent families of (k+1)-subsets of Fin n. -/
def higher_bruhat_inc (n k : ℕ) : Type :=
  {X : Finset (Finset (Fin n)) //
    (∀ A ∈ X, A.card = k + 1) ∧ higher_bruhat_packet_consistent n k X}
