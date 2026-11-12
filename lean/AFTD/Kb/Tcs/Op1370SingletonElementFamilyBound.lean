import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_singleton_element_family_bound

Topic: combinatorics   Node: ed1c794a6ff1

Provenance: original. Related work: arXiv:2611.12199, Conjecture 4.3, for a family consisting of a singleton set; the uncomplementedness assumption can be omitted in this case.

For at least three nonempty mutually strongly incomparable families of subsets of an n-element set, if one family consists of the single set {x} for some element x, their total size is at most 2^(n-1)-1. No uncomplementedness assumption is needed.
-/

theorem op_1370_singleton_element_family_bound (n t : ℕ) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (x : Fin n) (hi : 𝒜 i = {{x}}) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  open Finset in
  have hdisj : ∀ (j1 j2 : Fin t), j1 ≠ j2 → Disjoint (𝒜 j1) (𝒜 j2) := by
    intro j1 j2 hj
    rw [disjoint_iff_ne]
    intro A hA B hB heq
    subst heq
    exact hinc j1 j2 hj A hA A hB subset_rfl
  have hp : (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint 𝒜 :=
    fun j1 _ j2 _ hj => hdisj j1 j2 hj
  have hsum : ∑ j, (𝒜 j).card = (Finset.univ.biUnion 𝒜).card := by
    rw [Finset.card_biUnion hp]
  rw [hsum]
  set U : Finset (Fin n) := Finset.univ.erase x
  have hU : U.Nonempty := by
    by_contra hU'
    rw [Finset.nonempty_iff_ne_empty, not_not] at hU'
    have hex : ∃ j : Fin t, j ≠ i := by
      have hne' : (Finset.univ \ ({i} : Finset (Fin t))).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        have hsub : Finset.univ ⊆ ({i} : Finset (Fin t)) := by
          rw [Finset.sdiff_eq_empty_iff_subset] at h
          exact h
        have hle := Finset.card_le_card hsub
        rw [Finset.card_fin, Finset.card_singleton] at hle
        omega
      rcases hne' with ⟨j, hj⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
      exact ⟨j, hj.2⟩
    rcases hex with ⟨j, hij⟩
    rcases hne j with ⟨B, hB⟩
    have hx : x ∉ B := by
      intro hxB
      have hsub : ({x} : Finset (Fin n)) ⊆ B := Finset.singleton_subset_iff.mpr hxB
      have hxmem : ({x} : Finset (Fin n)) ∈ 𝒜 i := by rw [hi]; exact Finset.mem_singleton_self _
      exact hinc i j (Ne.symm hij) {x} hxmem B hB hsub
    have hBU : B ⊆ U := by
      intro y hy
      rw [Finset.mem_erase]
      exact ⟨fun hyx => hx (hyx ▸ hy), Finset.mem_univ y⟩
    rw [hU', Finset.subset_empty] at hBU
    have hBempty : B ⊆ ({x} : Finset (Fin n)) := by rw [hBU]; exact Finset.empty_subset _
    have hxmem : ({x} : Finset (Fin n)) ∈ 𝒜 i := by rw [hi]; exact Finset.mem_singleton_self _
    exact hinc j i hij B hB {x} hxmem hBempty
  have hsub : Finset.univ.biUnion 𝒜 ⊆ insert {x} (Finset.powerset U \ {∅, U}) := by
    intro S hS
    rw [Finset.mem_biUnion] at hS
    rcases hS with ⟨j, -, hjS⟩
    by_cases hij : j = i
    · subst hij
      rw [hi, Finset.mem_singleton] at hjS
      subst hjS
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_sdiff, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton, not_or]
      have hx : x ∉ S := by
        intro hxS
        have hsub : ({x} : Finset (Fin n)) ⊆ S := Finset.singleton_subset_iff.mpr hxS
        have hxmem : ({x} : Finset (Fin n)) ∈ 𝒜 i := by rw [hi]; exact Finset.mem_singleton_self _
        exact hinc i j (Ne.symm hij) {x} hxmem S hjS hsub
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase]
        exact ⟨fun hyx => hx (hyx ▸ hy), Finset.mem_univ y⟩
      · intro hSempty
        have hsub : S ⊆ ({x} : Finset (Fin n)) := by rw [hSempty]; exact Finset.empty_subset _
        have hxmem : ({x} : Finset (Fin n)) ∈ 𝒜 i := by rw [hi]; exact Finset.mem_singleton_self _
        exact hinc j i hij S hjS {x} hxmem hsub
      · intro hSU
        have hex : ∃ k : Fin t, k ≠ i ∧ k ≠ j := by
          have hne' : (Finset.univ \ ({i, j} : Finset (Fin t))).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro h
            have hsub : Finset.univ ⊆ ({i, j} : Finset (Fin t)) := by
              rw [Finset.sdiff_eq_empty_iff_subset] at h
              exact h
            have hle := Finset.card_le_card hsub
            rw [Finset.card_fin] at hle
            have h2 : ({i, j} : Finset (Fin t)).card ≤ 2 := Finset.card_le_two
            omega
          rcases hne' with ⟨k, hk⟩
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          exact ⟨k, hk.2.1, hk.2.2⟩
        rcases hex with ⟨k, hki, hkj⟩
        rcases hne k with ⟨D, hD⟩
        have hxD : x ∉ D := by
          intro hxD
          have hsub : ({x} : Finset (Fin n)) ⊆ D := singleton_subset_iff.mpr hxD
          have hxmem : ({x} : Finset (Fin n)) ∈ 𝒜 i := by rw [hi]; exact Finset.mem_singleton_self _
          exact hinc i k (Ne.symm hki) {x} hxmem D hD hsub
        have hDU : D ⊆ U := by
          intro y hy
          rw [Finset.mem_erase]
          exact ⟨fun hyx => hxD (hyx ▸ hy), Finset.mem_univ y⟩
        have hDS : D ⊆ S := by rw [hSU]; exact hDU
        exact hinc k j hkj D hD S hjS hDS
  have hcard_le : (Finset.univ.biUnion 𝒜).card ≤ (insert {x} (Finset.powerset U \ {∅, U})).card :=
    Finset.card_le_card hsub
  have hnotmem : ({x} : Finset (Fin n)) ∉ Finset.powerset U \ {∅, U} := by
    intro h
    rw [Finset.mem_sdiff, Finset.mem_powerset] at h
    have : x ∈ ({x} : Finset (Fin n)) := Finset.mem_singleton_self x
    have hxU := h.1 this
    rw [Finset.mem_erase] at hxU
    exact hxU.1 rfl
  have hne : (∅ : Finset (Fin n)) ≠ U := by
    intro h
    have := hU.ne_empty
    exact this h.symm
  have hsub_pow : ({∅, U} : Finset (Finset (Fin n))) ⊆ Finset.powerset U := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_powerset.mpr (Finset.empty_subset U), Finset.mem_powerset.mpr subset_rfl⟩
  have h2 : ({∅, U} : Finset (Finset (Fin n))).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    exact hne
  have hUcard : U.card = n - 1 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_fin]
  have htarget : (insert {x} (Finset.powerset U \ {∅, U})).card = 2 ^ (n - 1) - 1 := by
    rw [Finset.card_insert_of_notMem hnotmem]
    rw [Finset.card_sdiff_of_subset hsub_pow]
    rw [h2]
    rw [Finset.card_powerset, hUcard]
    have hUpos : 1 ≤ U.card := Finset.card_pos.mpr hU
    rw [hUcard] at hUpos
    have : 2 ≤ 2 ^ (n - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hUpos
    omega
  rw [htarget] at hcard_le
  exact hcard_le
