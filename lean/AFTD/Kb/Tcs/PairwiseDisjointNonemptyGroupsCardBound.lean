import AFTD.Prelude

/-!
# pairwise_disjoint_nonempty_groups_card_bound

Topic: graphs   Node: 001ccbf34ee0

Provenance: helper lemma. OP-1957: aggregate barrier component bound.

In a pairwise-disjoint finite family of nonempty finite sets, each chosen set has at most the size of the union minus the number of other sets.
-/

theorem pairwise_disjoint_nonempty_groups_card_bound
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (I : Finset ι) (T : ι → Finset V) (j : ι)
    (hj : j ∈ I)
    (hdis : ∀ i ∈ I, ∀ l ∈ I, i ≠ l → Disjoint (T i) (T l))
    (hne : ∀ i ∈ I, (T i).Nonempty) :
    (T j).card + I.card ≤ (I.biUnion T).card + 1 := by
  classical
  have hpair : (I : Set ι).PairwiseDisjoint T := by
    intro a ha b hb hab
    exact hdis a ha b hb hab
  rw [Finset.card_biUnion hpair]
  have hsum : (I.erase j).card ≤ ∑ i ∈ I.erase j, (T i).card := by
    calc
      (I.erase j).card = ∑ _i ∈ I.erase j, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ I.erase j, (T i).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_pos.mpr (hne i (Finset.mem_of_mem_erase hi))
  have hs := Finset.sum_erase_add I (fun i => (T i).card) hj
  have hc := Finset.card_erase_add_one hj
  omega
