import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber55NonunitCollisionGap

/-!
# good_slopes_fiber55_eleven_collision_gap

Topic: elementary_number_theory   Node: 932af6e186c9

Provenance: helper lemma. CRT collision reduction for the local fiber approach to OP-1027; the normalized case was observed in experiment 27539.

Let S be any finite set of points over Z/55Z. If a unit direction has a collision between distinct points whose first-coordinate difference is divisible by 11, then S has at most 30 good unit directions.
-/

theorem good_slopes_fiber55_eleven_collision_gap_ten (a : ZMod 55) (ha : a.val.Coprime 55) :
    10 ≤ (((Finset.range 11).image (fun k : ℕ => a + (5:ZMod 55)*(k:ZMod 55))).filter (fun b => b.val.Coprime 55)).card := by
  revert a
  decide

theorem good_slopes_fiber55_eleven_collision_gap (S : Finset (ZMod 55 × ZMod 55)) (a : ZMod 55) (ha : IsUnit a) (p q : ZMod 55 × ZMod 55) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) (hcollision : p.2 + a*p.1 = q.2 + a*q.1) (hdiv : ZMod.castHom (by decide : 11 ∣ 55) (ZMod 11) (q.1-p.1) = 0) : (good_slopes_point_directions 55 S).card ≤ 30 := by
  classical
  set d : ZMod 55 := q.1 - p.1 with hd
  have h11 : 11 ∣ d.val := by
    rw [hd]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hdiv
    exact (ZMod.natCast_eq_zero_iff d.val 11).mp hdiv
  obtain ⟨m, hm⟩ : ∃ m : ZMod 55, d = 11 * m := by
    obtain ⟨k, hk⟩ := h11
    use k
    conv_lhs => rw [← ZMod.natCast_zmod_val d]
    rw [hk]
    push_cast
    ring
  set U : Finset (ZMod 55) := Finset.univ.filter (fun b => IsUnit b) with hU
  have hUcard : U.card = 40 := by rw [hU]; exact good_slopes_fiber55_nonunit_collision_gap_card_units
  have hgoodU : good_slopes_point_directions 55 S ⊆ U := by
    intro b hb
    rw [good_slopes_point_directions] at hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [hU]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1⟩
  have ha_coprime : a.val.Coprime 55 := by
    have h := (ZMod.isUnit_iff_coprime a.val 55).mp
    have heq : ((a.val : ℕ) : ZMod 55) = a := ZMod.natCast_zmod_val a
    rw [heq] at h
    exact h ha
  set T : Finset (ZMod 55) := (((Finset.range 11).image (fun k : ℕ => a + (5:ZMod 55)*(k:ZMod 55))).filter (fun b => b.val.Coprime 55)) with hT
  have hTc : 10 ≤ T.card := by rw [hT]; exact good_slopes_fiber55_eleven_collision_gap_ten a ha_coprime
  have hTsub : T ⊆ U := by
    intro b hb
    rw [hT] at hb
    simp only [Finset.mem_filter] at hb
    rw [hU]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := (ZMod.isUnit_iff_coprime b.val 55).mpr hb.2
    have heq : ((b.val : ℕ) : ZMod 55) = b := ZMod.natCast_zmod_val b
    rw [heq] at h
    exact h
  have hTbad : ∀ b ∈ T, b ∉ good_slopes_point_directions 55 S := by
    intro b hb
    rw [hT] at hb
    simp only [Finset.mem_filter] at hb
    obtain ⟨hbimg, -⟩ := hb
    rw [Finset.mem_image] at hbimg
    obtain ⟨k, hk, hkb⟩ := hbimg
    intro hbgood
    rw [good_slopes_point_directions] at hbgood
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbgood
    obtain ⟨-, hbinj⟩ := hbgood
    have hzero : (b - a) * d = 0 := by
      rw [← hkb]
      have hsub : (a + (5:ZMod 55)*(k:ZMod 55)) - a = (5:ZMod 55)*(k:ZMod 55) := by ring
      rw [hsub, hm]
      have heq : (5:ZMod 55)*(k:ZMod 55)*(11*(m:ZMod 55)) = ((55:ℕ):ZMod 55) * ((k:ZMod 55)*(m:ZMod 55)) := by ring
      rw [heq, ZMod.natCast_self 55, zero_mul]
    have hval : p.2 + b * p.1 = q.2 + b * q.1 := by
      rw [hd] at hzero
      linear_combination hcollision - hzero
    exact hpq (hbinj (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hval)
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
