import AFTD.Prelude

/-!
# subgroup_units_pow_card_dvd

Topic: information   Node: 1397b1aa2848

Provenance: helper lemma. step towards subgroup_rigidity_order_of_mds

For a subgroup H of Lˣ where [L:F] = k and |F| = q, any divisor d of |H| satisfies q^k ≡ 1 (mod d).
-/

/-- In a degree-k extension L/F of a size-q field, any divisor d of the order of a subgroup of Lˣ satisfies q^k = 1 in ZMod d. -/
theorem subgroup_units_pow_card_dvd {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] (q n k : ℕ) (H : Subgroup Lˣ) [Fintype H] (hH_card : Fintype.card H = n) (hq : Fintype.card F = q) (hdim : Module.finrank F L = k) (hk : 2 ≤ k) (d : ℕ) (hdn : d ∣ n) (hd : 1 < d) : (q : ZMod d) ^ k = 1 := by
  have _ := hd
  have : Module.Finite F L := by
    have : 0 < Module.finrank F L := by omega
    exact Module.finite_of_finrank_pos this
  have : Finite L := Module.finite_of_finite F
  have hL_card : Nat.card L = q ^ k := by
    cases nonempty_fintype L
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := L), hq, hdim]
  have hH_dvd : Nat.card H ∣ Nat.card Lˣ := Subgroup.card_subgroup_dvd_card H
  rw [Nat.card_units, hL_card] at hH_dvd
  rw [Nat.card_eq_fintype_card, hH_card] at hH_dvd
  have hd_dvd : d ∣ q ^ k - 1 := dvd_trans hdn hH_dvd
  have hq_pos : 0 < q := by
    have : 0 < Fintype.card F := Fintype.card_pos
    omega
  have hqk_pos : 0 < q ^ k := pow_pos hq_pos k
  obtain ⟨m, hm⟩ := hd_dvd
  have h : q ^ k = d * m + 1 := by omega
  have h' : ((q ^ k : ℕ) : ZMod d) = ((d * m + 1 : ℕ) : ZMod d) := by rw [h]
  push_cast at h'
  simp at h'
  exact h'
