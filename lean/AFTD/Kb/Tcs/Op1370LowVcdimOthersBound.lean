import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableStrictShattering
import AFTD.Kb.Tcs.Op1370UncomplementedShattererOthersBound

/-!
# op_1370_low_vcdim_others_bound

Topic: combinatorics   Node: ee3fa517ac80

Provenance: original. Related work: Low-shattering-dimension partial case of arXiv:2611.12199, Conjecture 4.3; no uncomplementedness is needed outside the designated family.

For at least three nonempty mutually strongly incomparable families of subsets of Fin n, with n at least three, suppose one designated family is uncomplemented and the union of the others has VC dimension strictly less than ceil(n/2). Then the total size is at most 2^(n-1)-1. No uncomplementedness is required of the other families.
-/

open Finset
set_option maxHeartbeats 1000000

lemma op1370_vc_shatterer_uncomp (n : ℕ) (F : Finset (Finset (Fin n)))
    (hvc : F.vcDim < (n + 1) / 2) : is_uncomplemented F.shatterer := by
  classical
  intro S hS hSc
  have hs := (Finset.mem_shatterer.mp hS).card_le_vcDim
  have hsc := (Finset.mem_shatterer.mp hSc).card_le_vcDim
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hsum : S.card + (Sᶜ).card = n := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  omega

theorem op_1370_low_vcdim_others_bound (n t : ℕ) (hn : 3 ≤ n) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (hunc : is_uncomplemented (𝒜 i)) (hvc : ((Finset.univ.erase i).biUnion 𝒜).vcDim < (n + 1) / 2) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  apply op_1370_uncomplemented_shatterer_others_bound n t hn ht 𝒜 hne hinc i hunc
  exact op1370_vc_shatterer_uncomp n ((Finset.univ.erase i).biUnion 𝒜) hvc
