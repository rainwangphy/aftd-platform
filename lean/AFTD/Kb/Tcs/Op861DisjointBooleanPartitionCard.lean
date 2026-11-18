import AFTD.Prelude

/-!
# op861_disjoint_boolean_partition_card

Topic: graphs   Node: 6e9e9bcdf9f1

Provenance: helper lemma. Cardinal arithmetic for op861_disjoint_boolean_windows_count.

For pairwise disjoint finite blocks, the number of Boolean outside assignments times the product of Boolean assignment counts on the blocks equals the total number of Boolean assignments.
-/

open scoped BigOperators

theorem op861_disjoint_boolean_partition_card (β ι : Type) [Fintype β] [DecidableEq β] [DecidableEq ι]
  (J : Finset ι) (B : ι → Finset β)
  (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (B i) (B j)) :
  Fintype.card ({t : β // t ∉ J.biUnion B} → Bool) *
    (∏ i ∈ J, 2 ^ (B i).card) = 2 ^ Fintype.card β := by
  classical
  have hU : (J.biUnion B).card ≤ Fintype.card β := Finset.card_le_univ _
  have h1 : Fintype.card {t : β // t ∉ J.biUnion B} = Fintype.card β - (J.biUnion B).card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have h2 : ∏ i ∈ J, 2 ^ (B i).card = 2 ^ (J.biUnion B).card := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.card_biUnion hdisj]
  rw [Fintype.card_fun, Fintype.card_bool, h1, h2, ← pow_add, Nat.sub_add_cancel hU]
