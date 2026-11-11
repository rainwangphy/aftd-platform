import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesPrime5AnchoredLine
import AFTD.Kb.NumberTheory.GoodSlopesPrime7AnchoredLine
import AFTD.Kb.NumberTheory.GoodSlopesPrime7FiveOnLine
import AFTD.Kb.NumberTheory.GoodSlopesFiber35AnchoredNeighbors

/-!
# good_slopes_fiber35_unit_gap

Topic: elementary_number_theory   Node: 0a991428c418

Provenance: helper lemma. A point-fiber strengthening of the two-prime gap used for OP-1027; related work arXiv:2611.01465, Theorem 8.3. Exhaustive constraint model recorded as experiment 21999.

For any 35 points over the residues modulo 35, if at least one unit direction fails to be injective, then at most 20 of the 24 unit directions are injective.
-/

namespace Gs35Gap

def U35 : Finset (ZMod 35) := {1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34}

theorem isUnit_iff_U (x : ZMod 35) : IsUnit x ↔ x ∈ U35 := by
  rw [isUnit_iff_exists_inv]; revert x; decide

theorem nonunit_four : ∀ a0 ∈ U35, ∀ d1 : ZMod 35, d1 ∉ U35 → d1 ≠ 0 →
    4 ≤ (U35.filter (fun b => -(a0 * d1) + b * d1 = 0)).card := by decide

theorem eight_sub : ({6,8,11,16,22,26,29,31} : Finset (ZMod 35)) ⊆ U35 := by decide

theorem one_not_eight : (1 : ZMod 35) ∉ ({6,8,11,16,22,26,29,31} : Finset (ZMod 35)) := by decide

theorem neg_one_eq : (-1 : ZMod 35) = 34 := by decide

end Gs35Gap

theorem good_slopes_fiber35_unit_gap (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35) (hbad : ∃ a : ZMod 35, IsUnit a ∧ a ∉ good_slopes_point_directions 35 S) : (good_slopes_point_directions 35 S).card ≤ 20 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨a0, ha0u, ha0⟩ := hbad
  have hmem : ∀ a, a ∈ good_slopes_point_directions 35 S ↔
      IsUnit a ∧ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S := by
    intro a; unfold good_slopes_point_directions; simp
  -- four bad unit directions are impossible
  have key : ∀ B : Finset (ZMod 35),
      (∀ b ∈ B, IsUnit b ∧ ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b * p.1) S) → B.card ≤ 3 := by
    intro B hB
    have hBU : B ⊆ Gs35Gap.U35 := fun b hb => (Gs35Gap.isUnit_iff_U b).1 (hB b hb).1
    have hsub : good_slopes_point_directions 35 S ⊆ Gs35Gap.U35 \ B := by
      intro a ha
      rw [hmem] at ha
      rw [Finset.mem_sdiff]
      exact ⟨(Gs35Gap.isUnit_iff_U a).1 ha.1, fun hb => (hB a hb).2 ha.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hBU] at h1
    have : Gs35Gap.U35.card = 24 := by decide
    omega
  have hni : ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a0 * p.1) S := by
    intro h; exact ha0 ((hmem a0).2 ⟨ha0u, h⟩)
  obtain ⟨p, hp, q, hq, hpq, hne⟩ : ∃ p ∈ S, ∃ q ∈ S, p.2 + a0 * p.1 = q.2 + a0 * q.1 ∧ p ≠ q := by
    simp only [Set.InjOn, not_forall] at hni
    obtain ⟨p, hp, q, hq, h, hne⟩ := hni
    exact ⟨p, hp, q, hq, h, hne⟩
  set d1 := q.1 - p.1 with hd1
  set d2 := q.2 - p.2 with hd2
  have hd : d2 = -(a0 * d1) := by rw [hd1, hd2]; linear_combination -hpq
  have bad_of : ∀ b, d2 + b * d1 = 0 → ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b * p.1) S := by
    intro b hb hinj
    exact hne (hinj hp hq (by simp only; rw [hd1, hd2] at hb; linear_combination -hb))
  by_cases hu1 : IsUnit d1
  · -- normalise the collision to (0,0), (1,34)
    have hd2u : IsUnit d2 := by rw [hd]; exact (ha0u.mul hu1).neg
    set s := d1⁻¹ with hs
    set r := -d2⁻¹ with hr
    have hsd : s * d1 = 1 := by rw [hs, mul_comm]; exact ZMod.mul_inv_of_unit d1 hu1
    have hrd : r * d2 = -1 := by rw [hr, neg_mul, mul_comm, ZMod.mul_inv_of_unit d2 hd2u]
    have hsu : IsUnit s := isUnit_iff_exists_inv.2 ⟨d1, hsd⟩
    have hru : IsUnit r := isUnit_iff_exists_inv.2 ⟨-d2, by rw [mul_neg, hrd, neg_neg]⟩
    let φ : ZMod 35 × ZMod 35 → ZMod 35 × ZMod 35 := fun u => (s * (u.1 - p.1), r * (u.2 - p.2))
    have hφ : Function.Injective φ := by
      intro u v h
      simp only [φ, Prod.mk.injEq] at h
      have e1 := hsu.mul_left_cancel h.1
      have e2 := hru.mul_left_cancel h.2
      exact Prod.ext (by linear_combination e1) (by linear_combination e2)
    set S' := S.image φ with hS'
    have hcard' : S'.card = 35 := by rw [hS', Finset.card_image_of_injective _ hφ, hcard]
    have h0 : ((0 : ZMod 35), (0 : ZMod 35)) ∈ S' :=
      Finset.mem_image.2 ⟨p, hp, by simp [φ]⟩
    have h1 : ((1 : ZMod 35), (34 : ZMod 35)) ∈ S' :=
      Finset.mem_image.2 ⟨q, hq, by
        simp only [φ, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [← hd1]; exact hsd
        · rw [← hd2, hrd, Gs35Gap.neg_one_eq]⟩
    -- a direction b bad on S' gives the direction a0 * b bad on S
    have transfer : ∀ b, ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b * p.1) S' →
        ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + (a0 * b) * p.1) S := by
      intro b hb hinj
      apply hb
      intro u' hu' v' hv' huv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
      have hrel : ∀ w : ZMod 35 × ZMod 35, (φ w).2 + b * (φ w).1 =
          r * (w.2 + (a0 * b) * w.1) - (r * p.2 + b * s * p.1) := by
        intro w
        simp only [φ]
        have hrs : r * a0 = s := by
          have : r * a0 * d1 = s * d1 := by
            rw [hsd, mul_assoc, ← neg_neg (a0 * d1), ← hd, mul_neg, hrd, neg_neg]
          exact hu1.mul_right_cancel this
        linear_combination (-(b * w.1)) * hrs
      have e : r * (u.2 + (a0 * b) * u.1) = r * (v.2 + (a0 * b) * v.1) := by
        have := huv; simp only at this; rw [hrel u, hrel v] at this; linear_combination this
      rw [hinj hu hv (hru.mul_left_cancel e)]
    apply good_slopes_fiber35_anchored_neighbors S'
      (fun a => Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S') h0 h1
    · intro a _ ha; exact ha
    · intro a _ ha t
      have himg : S'.image (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_image_of_injOn ha, hcard', ZMod.card]
      have ht : t ∈ S'.image (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) := by
        rw [himg]; exact Finset.mem_univ t
      obtain ⟨x, hx, hxt⟩ := Finset.mem_image.1 ht
      exact ⟨x, hx, hxt⟩
    · intro a b c ha hb hc hab hac hbc
      by_contra hall
      push Not at hall
      obtain ⟨hga, hgb, hgc⟩ := hall
      have hT : (insert (1 : ZMod 35) ({a, b, c} : Finset (ZMod 35))).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
        intro h1m
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1m
        rcases h1m with h | h | h <;> [exact Gs35Gap.one_not_eight (h ▸ ha); exact Gs35Gap.one_not_eight (h ▸ hb);
          exact Gs35Gap.one_not_eight (h ▸ hc)]
      have hB := key ((insert (1 : ZMod 35) ({a, b, c} : Finset (ZMod 35))).image (a0 * ·)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        have hyu : IsUnit y := by
          rcases hy with rfl | rfl | rfl | rfl
          · exact isUnit_one
          · exact (Gs35Gap.isUnit_iff_U _).2 (Gs35Gap.eight_sub ha)
          · exact (Gs35Gap.isUnit_iff_U _).2 (Gs35Gap.eight_sub hb)
          · exact (Gs35Gap.isUnit_iff_U _).2 (Gs35Gap.eight_sub hc)
        refine ⟨ha0u.mul hyu, ?_⟩
        rcases hy with rfl | rfl | rfl | rfl
        · simpa using hni
        · exact transfer _ hga
        · exact transfer _ hgb
        · exact transfer _ hgc)
      rw [Finset.card_image_of_injective _ ha0u.mul_right_injective, hT] at hB
      omega
  · -- a nonunit difference: four bad directions at once
    have hd10 : d1 ≠ 0 := by
      intro h0
      apply hne
      have h2 : d2 = 0 := by rw [hd, h0, mul_zero, neg_zero]
      exact Prod.ext (by linear_combination -h0) (by linear_combination -h2)
    have h4 := Gs35Gap.nonunit_four a0 ((Gs35Gap.isUnit_iff_U a0).1 ha0u) d1 (fun h => hu1 ((Gs35Gap.isUnit_iff_U d1).2 h)) hd10
    have := key (Gs35Gap.U35.filter (fun b => -(a0 * d1) + b * d1 = 0)) (by
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨(Gs35Gap.isUnit_iff_U b).2 hb.1, bad_of b (by rw [hd]; exact hb.2)⟩)
    omega
