import AFTD.Prelude

/-!
# op_1370_shattered_capacity

Topic: combinatorics   Node: 807e8842e9f7

Provenance: helper lemma. Counting reduction for the private-element case of OP-1370.

For set families B, C and D on a finite ground set V, assume each member of C is incomparable with every member of B, no member of D contains a member of B, and the complement within V of each member of C is absent from D. Then the cardinalities of C, D and the family shattered by B sum to at most 2^|V|.
-/

open Finset
set_option maxHeartbeats 800000

theorem op_1370_shattered_capacity {α : Type*} [DecidableEq α] (V : Finset α) (B C D : Finset (Finset α)) (hB : ∀ S ∈ B, S ⊆ V) (hC : ∀ S ∈ C, S ⊆ V) (hD : ∀ S ∈ D, S ⊆ V) (hCB : ∀ c ∈ C, ∀ b ∈ B, ¬ c ⊆ b ∧ ¬ b ⊆ c) (hDB : ∀ d ∈ D, ∀ b ∈ B, ¬ b ⊆ d) (hCD : ∀ c ∈ C, V \ c ∉ D) : C.card + D.card + B.shatterer.card ≤ 2 ^ V.card := by
  classical
  let P := V.powerset
  let H := P.filter (fun S => ∃ b ∈ B, b ⊆ S)
  let Q := P.filter (fun S => ∀ b ∈ B, ¬ S ⊆ b ∧ ¬ b ⊆ S)
  let Cbar := C.image (V \ ·)
  let Qbar := Q.image (V \ ·)
  let Tbar := B.shatterer.image (V \ ·)
  have hP : P.card = 2 ^ V.card := card_powerset V
  have hshV : ∀ s ∈ B.shatterer, s ⊆ V := by
    intro s hs
    obtain ⟨b, hb, hsb⟩ := (mem_shatterer.mp hs).exists_superset
    exact hsb.trans (hB b hb)
  have hQ : C ⊆ Q := by
    intro c hc
    apply mem_filter.mpr
    exact ⟨mem_powerset.mpr (hC c hc), hCB c hc⟩
  have hbar : Cbar ⊆ Qbar := image_subset_image hQ
  have hCbar : Cbar.card = C.card := by
    apply card_image_of_injOn
    intro a ha b hb he
    have h := congrArg (fun s : Finset α => V \ s) he
    rw [Finset.sdiff_sdiff_eq_self (hC a ha), Finset.sdiff_sdiff_eq_self (hC b hb)] at h
    exact h
  have hTbar : Tbar.card = B.shatterer.card := by
    apply card_image_of_injOn
    intro a ha b hb he
    have h := congrArg (fun s : Finset α => V \ s) he
    rw [Finset.sdiff_sdiff_eq_self (hshV a ha), Finset.sdiff_sdiff_eq_self (hshV b hb)] at h
    exact h
  have hH : H ⊆ P := filter_subset _ _
  have hCbarP : Cbar ⊆ P := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr (sdiff_subset)
  have hDP : D ⊆ P := by intro d hd; exact mem_powerset.mpr (hD d hd)
  have hdis : Disjoint D (H ∪ Cbar) := by
    rw [disjoint_left]
    intro d hd hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨_, b, hb, hbd⟩ := mem_filter.mp hm
      exact hDB d hd b hb hbd
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp hm
      exact hCD c hc hd
  have hcap := card_le_card (union_subset hDP (union_subset hH hCbarP))
  rw [card_union_of_disjoint hdis, hP] at hcap
  have hT : Tbar ⊆ H \ Qbar := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    have htV := hshV t ht
    have htsh := mem_shatterer.mp ht
    obtain ⟨b1, hb1, htb1⟩ := htsh.exists_superset
    obtain ⟨b0, hb0, ht0⟩ := htsh (empty_subset t)
    have hb0sub : b0 ⊆ V \ t := by
      intro z hz
      refine mem_sdiff.mpr ⟨hB b0 hb0 hz, ?_⟩
      intro hzt
      have hz0 : z ∈ t ∩ b0 := mem_inter.mpr ⟨hzt, hz⟩
      rw [ht0] at hz0
      exact notMem_empty _ hz0
    apply mem_sdiff.mpr
    constructor
    · apply mem_filter.mpr
      exact ⟨mem_powerset.mpr sdiff_subset, ⟨b0, hb0, hb0sub⟩⟩
    · intro hqbar
      obtain ⟨q, hq, he⟩ := mem_image.mp hqbar
      have hqV : q ⊆ V := mem_powerset.mp (mem_filter.mp hq).1
      have hqt : q = t := by
        have eq := congrArg (fun s : Finset α => V \ s) he
        rw [Finset.sdiff_sdiff_eq_self hqV, Finset.sdiff_sdiff_eq_self htV] at eq
        exact eq
      have hqinc := (mem_filter.mp hq).2 b1 hb1
      apply hqinc.1
      simpa [hqt] using htb1
  have htcard := card_le_card hT
  rw [hTbar] at htcard
  have hinter := card_le_card (inter_subset_inter_left (s := H) hbar)
  have hunion := card_union_add_card_inter H Cbar
  have hsplit := card_sdiff_add_card_inter H Qbar
  rw [hCbar] at hunion
  omega
