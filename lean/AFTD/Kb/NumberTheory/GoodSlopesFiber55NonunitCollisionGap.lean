import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_fiber55_nonunit_collision_gap

Topic: elementary_number_theory   Node: 3bdcd1ade620

Provenance: helper lemma. CRT collision reduction for the local fiber approach to OP-1027; experiment 27539 illustrates the stronger difference-11 case.

Let S be any finite set of points over Z/55Z. If a unit direction has a collision between distinct points whose first-coordinate difference is not a unit, then S has at most 36 good unit directions.
-/

lemma good_slopes_fiber55_nonunit_collision_gap_card_units :
    (Finset.univ.filter (fun b : ZMod 55 => IsUnit b)).card = 40 := by decide

lemma good_slopes_fiber55_nonunit_collision_gap_five :
    ∀ a : ZMod 55, IsUnit a →
      4 ≤ (((Finset.range 5).image (fun k : ℕ => a + (11:ZMod 55) * (k:ZMod 55))).filter (fun b => IsUnit b)).card := by
  decide

lemma good_slopes_fiber55_nonunit_collision_gap_eleven :
    ∀ a : ZMod 55, IsUnit a →
      4 ≤ (((Finset.range 11).image (fun k : ℕ => a + (5:ZMod 55) * (k:ZMod 55))).filter (fun b => IsUnit b)).card := by
  decide

theorem good_slopes_fiber55_nonunit_collision_gap (S : Finset (ZMod 55 × ZMod 55)) (a : ZMod 55) (ha : IsUnit a) (p q : ZMod 55 × ZMod 55) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) (hcollision : p.2 + a*p.1 = q.2 + a*q.1) (hnonunit : ¬ IsUnit (q.1-p.1)) : (good_slopes_point_directions 55 S).card ≤ 36 := by
  classical
  set d : ZMod 55 := q.1 - p.1 with hd
  have hd0 : d ≠ 0 := by
    intro h
    have h1 : q.1 = p.1 := by rw [hd] at h; exact sub_eq_zero.mp h
    have h2 : p.2 = q.2 := by rw [h1] at hcollision; exact add_right_cancel hcollision
    exact hpq (Prod.ext h1.symm h2)
  have hcoll : p.2 - q.2 = a * d := by
    rw [hd, mul_sub]
    linear_combination hcollision
  have hbad : ∀ b : ZMod 55, (b - a) * d = 0 → b ∉ good_slopes_point_directions 55 S := by
    intro b hb hbgood
    rw [good_slopes_point_directions] at hbgood
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbgood
    obtain ⟨hjunit, hbinj⟩ := hbgood
    have hval : p.2 + b * p.1 = q.2 + b * q.1 := by
      have hp1 : p.1 - q.1 = -d := by rw [hd]; ring
      have key : (p.2 - q.2) + b * (p.1 - q.1) = 0 := by
        rw [hcoll, hp1]
        have hab : a - b = -(b - a) := by ring
        have hzero : (a - b) * d = 0 := by rw [hab, neg_mul, hb, neg_zero]
        linear_combination hzero
      linear_combination key
    exact hpq (hbinj (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hval)
  have hnonunit' : ¬ Nat.Coprime d.val 55 := by
    intro hc
    apply hnonunit
    have hv : ((d.val : ℕ) : ZMod 55) = d := ZMod.natCast_zmod_val d
    rw [← hv]
    exact (ZMod.isUnit_iff_coprime d.val 55).mpr hc
  have hcase : 5 ∣ d.val ∨ 11 ∣ d.val := by
    by_contra h
    rw [not_or] at h
    apply hnonunit'
    have hcop : Nat.Coprime d.val (5 * 11) ↔ Nat.Coprime d.val 5 ∧ Nat.Coprime d.val 11 :=
      Nat.coprime_mul_iff_right (m := 5) (n := 11) (k := d.val)
    exact hcop.mpr ⟨((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h.1).symm,
                    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 11)).mpr h.2).symm⟩
  set U : Finset (ZMod 55) := Finset.univ.filter (fun b => IsUnit b) with hU
  have hUcard : U.card = 40 := by rw [hU]; exact good_slopes_fiber55_nonunit_collision_gap_card_units
  have hgoodU : good_slopes_point_directions 55 S ⊆ U := by
    intro b hb
    rw [good_slopes_point_directions] at hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [hU]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1⟩
  rcases hcase with h5 | h11
  · obtain ⟨m, hm⟩ := h5
    have hd5 : d = 5 * (m : ZMod 55) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val d]
      rw [hm]; push_cast; ring
    set T : Finset (ZMod 55) := ((Finset.range 5).image (fun k : ℕ => a + (11:ZMod 55)*(k:ZMod 55))).filter (fun b => IsUnit b) with hT
    have hTc : 4 ≤ T.card := by rw [hT]; exact good_slopes_fiber55_nonunit_collision_gap_five a ha
    have hTsub : T ⊆ U := by
      intro b hb
      rw [hT] at hb
      simp only [Finset.mem_filter] at hb
      rw [hU]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩
    have hTbad : ∀ b ∈ T, b ∉ good_slopes_point_directions 55 S := by
      intro b hb
      rw [hT] at hb
      simp only [Finset.mem_filter] at hb
      obtain ⟨hbimg, -⟩ := hb
      rw [Finset.mem_image] at hbimg
      obtain ⟨k, hk, hkb⟩ := hbimg
      rw [← hkb]
      apply hbad
      have hsub : (a + (11:ZMod 55)*(k:ZMod 55)) - a = (11:ZMod 55)*(k:ZMod 55) := by ring
      rw [hsub, hd5]
      have heq : (11:ZMod 55)*(k:ZMod 55)*(5*(m:ZMod 55)) = ((55:ℕ):ZMod 55) * ((k:ZMod 55)*(m:ZMod 55)) := by ring
      rw [heq, ZMod.natCast_self 55, zero_mul]
    have hdisj : Disjoint (good_slopes_point_directions 55 S) T := by
      rw [Finset.disjoint_left]
      intro x hx hxt
      exact hTbad x hxt hx
    have hunion_card : (good_slopes_point_directions 55 S ∪ T).card
        = (good_slopes_point_directions 55 S).card + T.card :=
      (Finset.card_union_eq_card_add_card).mpr hdisj
    have hle : (good_slopes_point_directions 55 S ∪ T).card ≤ 40 := by
      rw [← hUcard]
      exact Finset.card_le_card (Finset.union_subset hgoodU hTsub)
    omega
  · obtain ⟨m, hm⟩ := h11
    have hd11 : d = 11 * (m : ZMod 55) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val d]
      rw [hm]; push_cast; ring
    set T : Finset (ZMod 55) := ((Finset.range 11).image (fun k : ℕ => a + (5:ZMod 55)*(k:ZMod 55))).filter (fun b => IsUnit b) with hT
    have hTc : 4 ≤ T.card := by rw [hT]; exact good_slopes_fiber55_nonunit_collision_gap_eleven a ha
    have hTsub : T ⊆ U := by
      intro b hb
      rw [hT] at hb
      simp only [Finset.mem_filter] at hb
      rw [hU]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩
    have hTbad : ∀ b ∈ T, b ∉ good_slopes_point_directions 55 S := by
      intro b hb
      rw [hT] at hb
      simp only [Finset.mem_filter] at hb
      obtain ⟨hbimg, -⟩ := hb
      rw [Finset.mem_image] at hbimg
      obtain ⟨k, hk, hkb⟩ := hbimg
      rw [← hkb]
      apply hbad
      have hsub : (a + (5:ZMod 55)*(k:ZMod 55)) - a = (5:ZMod 55)*(k:ZMod 55) := by ring
      rw [hsub, hd11]
      have heq : (5:ZMod 55)*(k:ZMod 55)*(11*(m:ZMod 55)) = ((55:ℕ):ZMod 55) * ((k:ZMod 55)*(m:ZMod 55)) := by ring
      rw [heq, ZMod.natCast_self 55, zero_mul]
    have hdisj : Disjoint (good_slopes_point_directions 55 S) T := by
      rw [Finset.disjoint_left]
      intro x hx hxt
      exact hTbad x hxt hx
    have hunion_card : (good_slopes_point_directions 55 S ∪ T).card
        = (good_slopes_point_directions 55 S).card + T.card :=
      (Finset.card_union_eq_card_add_card).mpr hdisj
    have hle : (good_slopes_point_directions 55 S ∪ T).card ≤ 40 := by
      rw [← hUcard]
      exact Finset.card_le_card (Finset.union_subset hgoodU hTsub)
    omega
