import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35AnchoredNeighbors

/-!
# good_slopes_fiber35_bad_neighbors

Topic: elementary_number_theory   Node: 50760189a5a0

Provenance: helper lemma. A normalization and counting consequence of good_slopes_fiber35_anchored_neighbors; tested in experiment 22001.

For any 35 points modulo 35 and any bad unit direction, at least three of its eight unit directions sharing a residue modulo 5 or modulo 7 are also bad.
-/

namespace Gs35Nb

def U35 : Finset (ZMod 35) := {1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34}

theorem isUnit_iff_U (x : ZMod 35) : IsUnit x ↔ x ∈ U35 := by
  rw [isUnit_iff_exists_inv]; revert x; decide

theorem nonunit_four : ∀ a0 ∈ U35, ∀ d1 : ZMod 35, d1 ∉ U35 → d1 ≠ 0 →
    4 ≤ (U35.filter (fun b => -(a0 * d1) + b * d1 = 0)).card := by decide

theorem eight_sub : ({6,8,11,16,22,26,29,31} : Finset (ZMod 35)) ⊆ U35 := by decide

theorem one_not_eight : (1 : ZMod 35) ∉ ({6,8,11,16,22,26,29,31} : Finset (ZMod 35)) := by decide

theorem neg_one_eq : (-1 : ZMod 35) = 34 := by decide

def Nb (a0 : ZMod 35) : Finset (ZMod 35) :=
  U35.filter (fun b => b ≠ a0 ∧ (b.val % 5 = a0.val % 5 ∨ b.val % 7 = a0.val % 7))

theorem Nb_card : ∀ a0 ∈ U35, (Nb a0).card = 8 := by decide

theorem nonunit_three : ∀ a0 ∈ U35, ∀ d1 : ZMod 35, d1 ∉ U35 → d1 ≠ 0 →
    3 ≤ ((Nb a0).filter (fun b => -(a0 * d1) + b * d1 = 0)).card := by decide

theorem eight_Nb : ∀ a0 ∈ U35, ∀ x ∈ ({6,8,11,16,22,26,29,31} : Finset (ZMod 35)), a0 * x ∈ Nb a0 := by
  decide

end Gs35Nb

theorem good_slopes_fiber35_bad_neighbors (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35)
  (a : ZMod 35) (ha : IsUnit a) (hbad : a ∉ good_slopes_point_directions 35 S) :
  ((good_slopes_point_directions 35 S).filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5 := by
  classical
  by_contra hlt
  push Not at hlt
  set a0 := a with ha0def
  have ha0u : IsUnit a0 := ha
  have ha0 := hbad
  have hmem : ∀ a, a ∈ good_slopes_point_directions 35 S ↔
      IsUnit a ∧ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a * p.1) S := by
    intro a; unfold good_slopes_point_directions; simp
  -- three bad neighbours are impossible
  have hU0 : a0 ∈ Gs35Nb.U35 := (Gs35Nb.isUnit_iff_U a0).1 ha0u
  have key : ∀ B : Finset (ZMod 35), B ⊆ Gs35Nb.Nb a0 →
      (∀ b ∈ B, ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b * p.1) S) → B.card ≤ 2 := by
    intro B hBN hB
    have hsub : (good_slopes_point_directions 35 S).filter
        (fun b => b ≠ a0 ∧ (b.val % 5 = a0.val % 5 ∨ b.val % 7 = a0.val % 7)) ⊆ Gs35Nb.Nb a0 \ B := by
      intro b hb
      rw [Finset.mem_filter, hmem] at hb
      rw [Finset.mem_sdiff]
      refine ⟨?_, fun hbB => hB b hbB hb.1.2⟩
      unfold Gs35Nb.Nb; rw [Finset.mem_filter]
      exact ⟨(Gs35Nb.isUnit_iff_U b).1 hb.1.1, hb.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hBN, Gs35Nb.Nb_card a0 hU0] at h1
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
        · rw [← hd2, hrd, Gs35Nb.neg_one_eq]⟩
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
      have hT : ({a, b, c} : Finset (ZMod 35)).card = 3 := Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
      have hB := key (({a, b, c} : Finset (ZMod 35)).image (a0 * ·)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact Gs35Nb.eight_Nb a0 hU0 _ ha
        · exact Gs35Nb.eight_Nb a0 hU0 _ hb
        · exact Gs35Nb.eight_Nb a0 hU0 _ hc) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
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
    have h3 := Gs35Nb.nonunit_three a0 hU0 d1 (fun h => hu1 ((Gs35Nb.isUnit_iff_U d1).2 h)) hd10
    have := key ((Gs35Nb.Nb a0).filter (fun b => -(a0 * d1) + b * d1 = 0)) (Finset.filter_subset _ _) (by
      intro b hb
      rw [Finset.mem_filter] at hb
      exact bad_of b (by rw [hd]; exact hb.2))
    omega
