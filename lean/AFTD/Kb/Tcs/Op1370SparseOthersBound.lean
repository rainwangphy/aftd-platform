import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableStrictShattering
import AFTD.Kb.Tcs.Op1370SmallFamilyShattererUncomplemented
import AFTD.Kb.Tcs.Op1370UncomplementedShattererOthersBound

/-!
# op_1370_sparse_others_bound

Topic: combinatorics   Node: 62b49ce2e4c1

Provenance: original. Related work: Sparse-other-families case of arXiv:2611.12199, Conjecture 4.3; no uncomplementedness is needed outside the designated family.

For at least three nonempty mutually strongly incomparable families of subsets of Fin n, with n at least three, suppose one designated family is uncomplemented and the total size of all the other families is less than 2^ceil(n/2). Then the total size is at most 2^(n-1)-1. No uncomplementedness of the other families is required.
-/

theorem op_1370_sparse_others_bound (n t : ℕ) (hn : 3 ≤ n) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (hunc : is_uncomplemented (𝒜 i)) (hsmall : (∑ j ∈ Finset.univ.erase i, (𝒜 j).card) < 2 ^ ((n + 1) / 2)) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  apply op_1370_uncomplemented_shatterer_others_bound n t hn ht 𝒜 hne hinc i hunc
  apply op_1370_small_family_shatterer_uncomplemented
  exact lt_of_le_of_lt Finset.card_biUnion_le hsmall
