import AFTD.Prelude

/-!
# op309_clean_component_charge_count

Topic: graphs   Node: 7fb468ca04ab

Provenance: helper lemma. OP-309 clean-component charging argument.

If every path component is charged to a bad path or bad star, each bad path has at most nine charges, each bad star at most ten, there are at most 2b bad components, and at most s of them are stars, then there are at most 18b+s paths.
-/

theorem op309_clean_component_charge_count
    {C : Type*} [DecidableEq C]
    (P Bp Bs : Finset C) (T : C → Finset C) (b s : ℕ)
    (hcover : P ⊆ (Bp ∪ Bs).biUnion T)
    (hp : ∀ x ∈ Bp, (T x).card ≤ 9)
    (hs : ∀ x ∈ Bs, (T x).card ≤ 10)
    (hbad : Bp.card + Bs.card ≤ 2*b) (hstar : Bs.card ≤ s) :
    P.card ≤ 18*b + s := by
  have h1 : P.card ≤ ((Bp ∪ Bs).biUnion T).card := Finset.card_le_card hcover
  have h2 : ((Bp ∪ Bs).biUnion T).card ≤ (Bp.biUnion T).card + (Bs.biUnion T).card := by
    rw [Finset.union_biUnion]; exact Finset.card_union_le _ _
  have h3 : (Bp.biUnion T).card ≤ Bp.card * 9 := by
    calc _ ≤ ∑ x ∈ Bp, (T x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Bp, 9 := Finset.sum_le_sum hp
      _ = Bp.card * 9 := by rw [Finset.sum_const, smul_eq_mul]
  have h4 : (Bs.biUnion T).card ≤ Bs.card * 10 := by
    calc _ ≤ ∑ x ∈ Bs, (T x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Bs, 10 := Finset.sum_le_sum hs
      _ = Bs.card * 10 := by rw [Finset.sum_const, smul_eq_mul]
  omega
