import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber21AnchoredClassification

/-!
# good_slopes_fiber21_bad_row_triple

Topic: elementary_number_theory   Node: f0d33560f84b

Provenance: helper lemma. CRT point-fiber classification for OP-1027; experiments 21996 and 21998 enumerate the possible bad-direction sets.

For 21 points over the residues modulo 21, suppose every unit direction congruent to 2 modulo 3 is injective, direction 1 is not injective, and at least nine unit directions are injective. Then the bad unit directions are exactly 1, 4, and 16.
-/

namespace Gs21Row

def U21 : Finset (ZMod 21) := {1,2,4,5,8,10,11,13,16,17,19,20}

theorem isUnit_iff_U (x : ZMod 21) : IsUnit x ↔ x ∈ U21 := by
  rw [isUnit_iff_exists_inv]; revert x; decide

theorem nonunit_cases : ∀ d1 : ZMod 21, d1 ∉ U21 → d1 ≠ 0 →
    (8 - 1) * d1 = 0 ∨ ∀ b ∈ ({4,10,13,16,19} : Finset (ZMod 21)), (b - 1) * d1 = 0 := by decide

theorem row_mem : ∀ a ∈ ({2,5,8,11,17,20} : Finset (ZMod 21)), a ∈ U21 ∧ a.val % 3 = 2 := by decide

theorem five_sub : ({4,10,13,16,19} : Finset (ZMod 21)) ⊆ U21 := by decide

theorem neg_one_eq : (-1 : ZMod 21) = 20 := by decide

end Gs21Row

theorem good_slopes_fiber21_bad_row_triple (S : Finset (ZMod 21 × ZMod 21)) (hcard : S.card = 21) (hrow : ∀ a : ZMod 21, IsUnit a → a.val % 3 = 2 → a ∈ good_slopes_point_directions 21 S) (hbad : (1 : ZMod 21) ∉ good_slopes_point_directions 21 S) (hlarge : 9 ≤ (good_slopes_point_directions 21 S).card) : ∀ a : ZMod 21, IsUnit a → (a ∉ good_slopes_point_directions 21 S ↔ a = 1 ∨ a = 4 ∨ a = 16) := by
  classical
  have hmem : ∀ a, a ∈ good_slopes_point_directions 21 S ↔
      IsUnit a ∧ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + a * p.1) S := by
    intro a; unfold good_slopes_point_directions; simp
  -- at most three bad unit directions
  have key : ∀ B : Finset (ZMod 21),
      (∀ b ∈ B, IsUnit b ∧ ¬ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + b * p.1) S) → B.card ≤ 3 := by
    intro B hB
    have hBU : B ⊆ Gs21Row.U21 := fun b hb => (Gs21Row.isUnit_iff_U b).1 (hB b hb).1
    have hsub : good_slopes_point_directions 21 S ⊆ Gs21Row.U21 \ B := by
      intro a ha
      rw [hmem] at ha
      rw [Finset.mem_sdiff]
      exact ⟨(Gs21Row.isUnit_iff_U a).1 ha.1, fun hb => (hB a hb).2 ha.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hBU] at h1
    have : Gs21Row.U21.card = 12 := by decide
    omega
  have hgoodrow : ∀ a ∈ ({2,5,8,11,17,20} : Finset (ZMod 21)),
      Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + a * p.1) S := by
    intro a ha
    obtain ⟨hU, h3⟩ := Gs21Row.row_mem a ha
    exact ((hmem a).1 (hrow a ((Gs21Row.isUnit_iff_U a).2 hU) h3)).2
  have hni : ¬ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 1 * p.1) S := by
    intro h; exact hbad ((hmem 1).2 ⟨isUnit_one, h⟩)
  obtain ⟨p, hp, q, hq, hpq, hne⟩ : ∃ p ∈ S, ∃ q ∈ S, p.2 + 1 * p.1 = q.2 + 1 * q.1 ∧ p ≠ q := by
    simp only [Set.InjOn, not_forall] at hni
    obtain ⟨p, hp, q, hq, h, hne⟩ := hni
    exact ⟨p, hp, q, hq, h, hne⟩
  set d1 := q.1 - p.1 with hd1
  set d2 := q.2 - p.2 with hd2
  have hd : d2 = -d1 := by rw [hd1, hd2]; linear_combination -hpq
  have bad_of : ∀ b, (b - 1) * d1 = 0 → ¬ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + b * p.1) S := by
    intro b hb hinj
    have hb' : d2 + b * d1 = 0 := by rw [hd]; linear_combination hb
    exact hne (hinj hp hq (by simp only; rw [hd1, hd2] at hb'; linear_combination -hb'))
  -- the transfer to the normalised set
  have main : Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 10 * p.1) S ∧
      Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 13 * p.1) S ∧
      Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 19 * p.1) S ∧
      ¬ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 4 * p.1) S ∧
      ¬ Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + 16 * p.1) S := by
    by_cases hu1 : IsUnit d1
    · set s := d1⁻¹ with hs
      have hsd : s * d1 = 1 := by rw [hs, mul_comm]; exact ZMod.mul_inv_of_unit d1 hu1
      have hsu : IsUnit s := isUnit_iff_exists_inv.2 ⟨d1, hsd⟩
      let φ : ZMod 21 × ZMod 21 → ZMod 21 × ZMod 21 := fun u => (s * (u.1 - p.1), s * (u.2 - p.2))
      have hφ : Function.Injective φ := by
        intro u v h
        simp only [φ, Prod.mk.injEq] at h
        have e1 := hsu.mul_left_cancel h.1
        have e2 := hsu.mul_left_cancel h.2
        exact Prod.ext (by linear_combination e1) (by linear_combination e2)
      set S' := S.image φ with hS'
      have hcard' : S'.card = 21 := by rw [hS', Finset.card_image_of_injective _ hφ, hcard]
      have h0 : ((0 : ZMod 21), (0 : ZMod 21)) ∈ S' :=
        Finset.mem_image.2 ⟨p, hp, by simp [φ]⟩
      have h1 : ((1 : ZMod 21), (20 : ZMod 21)) ∈ S' :=
        Finset.mem_image.2 ⟨q, hq, by
          simp only [φ, Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · rw [← hd1]; exact hsd
          · rw [← hd2, hd, mul_neg, hsd, Gs21Row.neg_one_eq]⟩
      have transfer : ∀ b, Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + b * p.1) S' ↔
          Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + b * p.1) S := by
        intro b
        have hrel : ∀ w : ZMod 21 × ZMod 21, (φ w).2 + b * (φ w).1 =
            s * (w.2 + b * w.1) - s * (p.2 + b * p.1) := by
          intro w; simp only [φ]; ring
        constructor
        · intro hinj u hu v hv huv
          apply hφ
          apply hinj (Finset.mem_image_of_mem φ hu) (Finset.mem_image_of_mem φ hv)
          simp only at huv ⊢
          rw [hrel u, hrel v, huv]
        · intro hinj u' hu' v' hv' huv
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
          have e : s * (u.2 + b * u.1) = s * (v.2 + b * v.1) := by
            have := huv; simp only at this; rw [hrel u, hrel v] at this; linear_combination this
          rw [hinj hu hv (hsu.mul_left_cancel e)]
      by_contra hn
      apply good_slopes_fiber21_anchored_classification S'
        (fun a => Set.InjOn (fun p : ZMod 21 × ZMod 21 => p.2 + a * p.1) S') h0 h1
      · intro a ha; exact (transfer a).2 (hgoodrow a ha)
      · intro a _ ha; exact ha
      · intro a _ ha t
        have himg : S'.image (fun p : ZMod 21 × ZMod 21 => p.2 + a * p.1) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_image_of_injOn ha, hcard', ZMod.card]
        have ht : t ∈ S'.image (fun p : ZMod 21 × ZMod 21 => p.2 + a * p.1) := by
          rw [himg]; exact Finset.mem_univ t
        obtain ⟨x, hx, hxt⟩ := Finset.mem_image.1 ht
        exact ⟨x, hx, hxt⟩
      · intro a b c ha hb hc hab hac hbc
        by_contra hall
        push Not at hall
        obtain ⟨hga, hgb, hgc⟩ := hall
        have hT : (insert (1 : ZMod 21) ({a, b, c} : Finset (ZMod 21))).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
          intro h1m
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1m
          have h1n : (1 : ZMod 21) ∉ ({4,10,13,16,19} : Finset (ZMod 21)) := by decide
          rcases h1m with h | h | h
          · exact h1n (h ▸ ha)
          · exact h1n (h ▸ hb)
          · exact h1n (h ▸ hc)
        have hB := key (insert (1 : ZMod 21) ({a, b, c} : Finset (ZMod 21))) (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨isUnit_one, hni⟩
          · exact ⟨(Gs21Row.isUnit_iff_U _).2 (Gs21Row.five_sub ha), fun h => hga ((transfer _).2 h)⟩
          · exact ⟨(Gs21Row.isUnit_iff_U _).2 (Gs21Row.five_sub hb), fun h => hgb ((transfer _).2 h)⟩
          · exact ⟨(Gs21Row.isUnit_iff_U _).2 (Gs21Row.five_sub hc), fun h => hgc ((transfer _).2 h)⟩)
        omega
      · simp only [transfer]
        tauto
    · exfalso
      have hd10 : d1 ≠ 0 := by
        intro h0
        apply hne
        have h2 : d2 = 0 := by rw [hd, h0, neg_zero]
        exact Prod.ext (by linear_combination -h0) (by linear_combination -h2)
      rcases Gs21Row.nonunit_cases d1 (fun h => hu1 ((Gs21Row.isUnit_iff_U d1).2 h)) hd10 with h8 | hall
      · exact bad_of 8 h8 (hgoodrow 8 (by decide))
      · have := key (insert (1 : ZMod 21) ({4,10,13,16,19} : Finset (ZMod 21))) (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | hx
          · exact ⟨isUnit_one, hni⟩
          · have hx' : x ∈ ({4,10,13,16,19} : Finset (ZMod 21)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx
            exact ⟨(Gs21Row.isUnit_iff_U _).2 (Gs21Row.five_sub hx'), bad_of x (hall x hx')⟩)
        have hc : (insert (1 : ZMod 21) ({4,10,13,16,19} : Finset (ZMod 21))).card = 6 := by decide
        omega
  obtain ⟨g10, g13, g19, b4, b16⟩ := main
  intro a ha
  rw [Gs21Row.isUnit_iff_U] at ha
  rw [hmem]
  simp only [Gs21Row.U21, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · constructor
    · intro _; decide
    · intro _ h; exact hni (by simpa using h.2)
  · have hg := hgoodrow (2 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (2 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
  · constructor
    · intro _; decide
    · intro _ h; exact b4 h.2
  · have hg := hgoodrow (5 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (5 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
  · have hg := hgoodrow (8 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (8 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
  · constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (10 : ZMod 21)).2 (by decide), g10⟩ h
    · intro h; exfalso; revert h; decide
  · have hg := hgoodrow (11 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (11 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
  · constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (13 : ZMod 21)).2 (by decide), g13⟩ h
    · intro h; exfalso; revert h; decide
  · constructor
    · intro _; decide
    · intro _ h; exact b16 h.2
  · have hg := hgoodrow (17 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (17 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
  · constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (19 : ZMod 21)).2 (by decide), g19⟩ h
    · intro h; exfalso; revert h; decide
  · have hg := hgoodrow (20 : ZMod 21) (by decide)
    constructor
    · intro h; exact absurd ⟨(Gs21Row.isUnit_iff_U (20 : ZMod 21)).2 (by decide), hg⟩ h
    · intro h; exfalso; revert h; decide
