import AFTD.Prelude

/-!
# op1370_zero_fiber_count

Topic: combinatorics   Node: c854dfbd9793

Provenance: helper lemma. Zero-doubled-fiber counting lemma for OP-1370, arXiv:2611.12199 Conjecture 4.3.

For n at least three, if a family of subsets of Fin n omits the empty set, {x}, its complement, and the full set, and no x-erased fiber has both orientations present, then it has at most 2^(n-1)-2 members.
-/

lemma op1370_zero_fiber_count (n : ℕ) (hn : 3 ≤ n) (U : Finset (Finset (Fin n))) (x : Fin n)
    (h0 : (∅ : Finset (Fin n)) ∉ U) (h1 : ({x} : Finset (Fin n)) ∉ U)
    (h2 : (Finset.univ.erase x : Finset (Fin n)) ∉ U) (h3 : (Finset.univ : Finset (Fin n)) ∉ U)
    (hover : ((U.filter (fun s => x ∉ s)) ∩
      ((U.filter (fun s => x ∈ s)).image (fun s => s.erase x))).card = 0) :
    U.card ≤ 2 ^ (n - 1) - 2 := by
  open Finset in
  classical
  let V : Finset (Fin n) := univ.erase x
  let P := U.filter (fun s => x ∉ s)
  let Q0 := U.filter (fun s => x ∈ s)
  let Q := Q0.image (fun s => s.erase x)
  have hpq : P ∪ Q ⊆ V.powerset \ {∅, V} := by
    intro S hS
    have hxS : x ∉ S := by
      rcases mem_union.mp hS with hS | hS
      · exact (mem_filter.mp hS).2
      · obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
        simp
    have hsub : S ⊆ V := by
      intro y hy
      simp only [V, mem_erase, mem_univ, and_true]
      exact fun h => hxS (h ▸ hy)
    have hn0 : S ≠ ∅ := by
      intro h
      subst S
      rcases mem_union.mp hS with hp | hq
      · exact h0 (mem_filter.mp hp).1
      · obtain ⟨T, hT, heq⟩ := mem_image.mp hq
        have hTx : x ∈ T := (mem_filter.mp hT).2
        have hTeq : T = {x} := by
          have hi := insert_erase hTx
          rw [heq] at hi
          simpa using hi.symm
        exact h1 (hTeq ▸ (mem_filter.mp hT).1)
    have hnV : S ≠ V := by
      intro h
      subst S
      rcases mem_union.mp hS with hp | hq
      · exact h2 (mem_filter.mp hp).1
      · obtain ⟨T, hT, heq⟩ := mem_image.mp hq
        have hTx : x ∈ T := (mem_filter.mp hT).2
        have hTu : T = univ := by
          have hi := insert_erase hTx
          rw [heq] at hi
          simpa [V] using hi.symm
        exact h3 (hTu ▸ (mem_filter.mp hT).1)
    simp only [mem_sdiff, mem_powerset, mem_insert, mem_singleton, not_or]
    exact ⟨hsub, hn0, hnV⟩
  have hVcard : V.card = n - 1 := by simp [V]
  have hVne : V ≠ ∅ := by
    intro h
    have hc := congrArg Finset.card h
    simp [hVcard] at hc
    omega
  have hdel : ({∅, V} : Finset (Finset (Fin n))) ⊆ V.powerset := by
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_powerset.mpr (empty_subset V), mem_powerset.mpr subset_rfl⟩
  have hcarddel : ({∅, V} : Finset (Finset (Fin n))).card = 2 := by simp [hVne.symm]
  have hbound : (P ∪ Q).card ≤ 2 ^ (n - 1) - 2 := by
    have h := card_le_card hpq
    rw [card_sdiff_of_subset hdel, hcarddel, card_powerset, hVcard] at h
    exact h
  have hQcard : Q.card = Q0.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    have hax : x ∈ a := (mem_filter.mp ha).2
    have hbx : x ∈ b := (mem_filter.mp hb).2
    change a.erase x = b.erase x at hab
    calc
      a = insert x (a.erase x) := (insert_erase hax).symm
      _ = insert x (b.erase x) := by rw [hab]
      _ = b := insert_erase hbx
  have hsplit : P.card + Q0.card = U.card := by
    simpa [P, Q0, Nat.add_comm] using
      (card_filter_add_card_filter_not (s := U) (fun s => x ∈ s))
  have hPQ := card_union_add_card_inter P Q
  have hpow : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  change (P ∩ Q).card = 0 at hover
  omega
