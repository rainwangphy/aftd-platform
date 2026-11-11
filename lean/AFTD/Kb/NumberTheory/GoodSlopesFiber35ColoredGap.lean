import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35BadNeighbors
import AFTD.Kb.NumberTheory.GoodSlopesFiber35AnchoredWidthGap

/-!
# good_slopes_fiber35_colored_gap

Topic: elementary_number_theory   Node: 860cb22f397c

Provenance: helper lemma. Three-color point-fiber bottleneck for OP-1027, motivated by arXiv:2611.04551, Question 10.2. Exhaustive constraint search 22050 found no counterexample with 17 good directions; the threshold 16 search was inconclusive.

Let S be a set of 35 points over the residues modulo 35, colored with three colors. Suppose that within each color both the first coordinate and every unit-direction form y+ax are injective. If any unit direction fails to be injective on all of S, then at most 16 unit directions are injective on all of S.
-/

lemma good_slopes_fiber35_colored_gap_unit_normalize (x : ZMod 35) (hx : x ≠ 0) :
    ∃ u : ZMod 35, IsUnit u ∧ (u * x = 1 ∨ u * x = 5 ∨ u * x = 7) := by
  revert x
  decide

lemma good_slopes_fiber35_colored_gap_directions_image
    (S : Finset (ZMod 35 × ZMod 35)) (S' : Finset (ZMod 35 × ZMod 35)) (a0 : ZMod 35) (ha0 : IsUnit a0)
    (hdir : ∀ b : ZMod 35, b ∈ good_slopes_point_directions 35 S' ↔ a0 * b ∈ good_slopes_point_directions 35 S) :
    (good_slopes_point_directions 35 S).card = (good_slopes_point_directions 35 S').card := by
  have hinj : Function.Injective (fun b : ZMod 35 => a0 * b) := ha0.mul_right_injective
  have himg : good_slopes_point_directions 35 S = (good_slopes_point_directions 35 S').image (fun b => a0 * b) := by
    ext x
    rw [Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨a0_inv, ha0_inv⟩ := ha0.exists_left_inv
      use a0_inv * x
      have hx_eq : a0 * (a0_inv * x) = x := by
        calc a0 * (a0_inv * x) = (a0_inv * a0) * x := by ring
        _ = 1 * x := by rw [ha0_inv]
        _ = x := by ring
      refine ⟨?_, hx_eq⟩
      rw [hdir]
      rwa [hx_eq]
    · rintro ⟨b, hb, rfl⟩
      rwa [← hdir]
  rw [himg, Finset.card_image_of_injective _ hinj]

theorem good_slopes_fiber35_colored_gap (S : Finset (ZMod 35 × ZMod 35)) (c : (ZMod 35 × ZMod 35) → Fin 3) (hcard : S.card = 35) (hinput : ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.1 = q.1 → p = q) (hunit : ∀ a : ZMod 35, IsUnit a → ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.2 + a*p.1 = q.2 + a*q.1 → p = q) (hbad : ∃ a : ZMod 35, IsUnit a ∧ a ∉ good_slopes_point_directions 35 S) : (good_slopes_point_directions 35 S).card ≤ 16 := by
  classical
  rcases hbad with ⟨a0, ha0, hbad0⟩
  have hmem : ∀ (T : Finset (ZMod 35 × ZMod 35)) (b : ZMod 35),
      b ∈ good_slopes_point_directions 35 T ↔
      IsUnit b ∧ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b * p.1) T := by
    intro T b
    unfold good_slopes_point_directions
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hni : ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + a0 * p.1) S := by
    intro h; exact hbad0 ((hmem S a0).2 ⟨ha0, h⟩)
  simp only [Set.InjOn, not_forall] at hni
  rcases hni with ⟨p, hp, q, hq, heq, hne⟩
  have hd10 : q.1 - p.1 ≠ 0 := by
    intro hd1
    have hd1' : q.1 = p.1 := sub_eq_zero.mp hd1
    have hd2 : q.2 = p.2 := by
      calc q.2 = (q.2 + a0 * q.1) - a0 * q.1 := by ring
      _ = (p.2 + a0 * p.1) - a0 * p.1 := by rw [← heq, hd1']
      _ = p.2 := by ring
    exact hne (Prod.ext hd1'.symm hd2.symm)
  obtain ⟨u, hu, hd⟩ := good_slopes_fiber35_colored_gap_unit_normalize (q.1 - p.1) hd10
  set s := u
  set r := u * a0⁻¹
  have hinv : a0⁻¹ * a0 = 1 := by rw [mul_comm, ZMod.mul_inv_of_unit a0 ha0]
  have hr : IsUnit r := by
    rw [(Commute.all u a0⁻¹).isUnit_mul_iff]
    refine ⟨hu, isUnit_iff_exists_inv.2 ⟨a0, hinv⟩⟩
  have hrs : r * a0 = s := by
    dsimp [r, s]
    calc (u * a0⁻¹) * a0 = u * (a0⁻¹ * a0) := by ring
    _ = u * 1 := by rw [hinv]
    _ = u := by ring
  let φ : ZMod 35 × ZMod 35 → ZMod 35 × ZMod 35 := fun w => (s * (w.1 - p.1), r * (w.2 - p.2))
  have hφ : Function.Injective φ := by
    intro x y h
    simp only [φ, Prod.mk.injEq] at h
    have e1 := hu.mul_left_cancel h.1
    have e2 := hr.mul_left_cancel h.2
    have e1' : x.1 = y.1 := by linear_combination e1
    have e2' : x.2 = y.2 := by linear_combination e2
    exact Prod.ext e1' e2'
  set S' := S.image φ
  have hcard' : S'.card = 35 := by
    calc S'.card = S.card := Finset.card_image_of_injective S hφ
    _ = 35 := hcard
  have h0 : ((0 : ZMod 35), (0 : ZMod 35)) ∈ S' := by
    rw [Finset.mem_image]
    exact ⟨p, hp, by simp [φ]⟩
  have h1 : ((u * (q.1 - p.1)), - (u * (q.1 - p.1))) ∈ S' := by
    rw [Finset.mem_image]
    refine ⟨q, hq, ?_⟩
    simp only [φ, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    have hd2 : q.2 - p.2 = -(a0 * (q.1 - p.1)) := by linear_combination -heq
    dsimp [r]
    calc (u * a0⁻¹) * (q.2 - p.2) = (u * a0⁻¹) * -(a0 * (q.1 - p.1)) := by rw [hd2]
    _ = - (u * (a0⁻¹ * a0) * (q.1 - p.1)) := by ring
    _ = - (u * 1 * (q.1 - p.1)) := by rw [hinv]
    _ = - (u * (q.1 - p.1)) := by ring
  have hrel : ∀ b (w : ZMod 35 × ZMod 35),
      (φ w).2 + b * (φ w).1 = r * (w.2 + (a0 * b) * w.1) - (r * (p.2 + (a0 * b) * p.1)) := by
    intro b w
    simp only [φ]
    calc r * (w.2 - p.2) + b * (s * (w.1 - p.1))
      _ = r * (w.2 - p.2) + b * (r * a0 * (w.1 - p.1)) := by rw [hrs]
      _ = r * (w.2 + (a0 * b) * w.1) - r * (p.2 + (a0 * b) * p.1) := by ring
  have hx : ∀ X : ZMod 35, (S'.filter (fun P => P.1 = X)).card ≤ 3 := by
    intro X
    rw [Finset.filter_image, Finset.card_image_of_injective _ hφ]
    have hinj : Set.InjOn c ↑(S.filter (fun w => (φ w).1 = X)) := by
      intro w hw v hv hc
      rw [Finset.mem_coe, Finset.mem_filter] at hw hv
      have heqX : (φ w).1 = (φ v).1 := hw.2.trans hv.2.symm
      simp only [φ] at heqX
      have heq1 := hu.mul_left_cancel heqX
      have heq2 : w.1 = v.1 := by linear_combination heq1
      exact hinput w hw.1 v hv.1 hc heq2
    have h1 : (S.filter (fun w => (φ w).1 = X)).card = ((S.filter (fun w => (φ w).1 = X)).image c).card :=
      (Finset.card_image_of_injOn hinj).symm
    have h2 : ((S.filter (fun w => (φ w).1 = X)).image c).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ _
    rw [Fintype.card_fin] at h2
    omega
  have hline : (S'.filter (fun P => P.2 + P.1 = 0)).card ≤ 3 := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hφ]
    have hinj : Set.InjOn c ↑(S.filter (fun w => (φ w).2 + (φ w).1 = 0)) := by
      intro w hw v hv hc
      rw [Finset.mem_coe, Finset.mem_filter] at hw hv
      have heq0 : (φ w).2 + (φ w).1 = (φ v).2 + (φ v).1 := hw.2.trans hv.2.symm
      have hb1w := hrel 1 w
      have hb1v := hrel 1 v
      rw [mul_one] at hb1w hb1v
      have heqr : r * (w.2 + a0 * w.1) = r * (v.2 + a0 * v.1) := by
        linear_combination heq0 - hb1w + hb1v
      have heqv := hr.mul_left_cancel heqr
      exact hunit a0 ha0 w hw.1 v hv.1 hc heqv
    have h1 : (S.filter (fun w => (φ w).2 + (φ w).1 = 0)).card = ((S.filter (fun w => (φ w).2 + (φ w).1 = 0)).image c).card :=
      (Finset.card_image_of_injOn hinj).symm
    have h2 : ((S.filter (fun w => (φ w).2 + (φ w).1 = 0)).image c).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ _
    rw [Fintype.card_fin] at h2
    omega
  have hdir : ∀ b : ZMod 35, b ∈ good_slopes_point_directions 35 S' ↔ a0 * b ∈ good_slopes_point_directions 35 S := by
    intro b
    rw [hmem S' b, hmem S (a0 * b)]
    rw [(Commute.all a0 b).isUnit_mul_iff, and_iff_right ha0]
    apply and_congr_right
    intro _
    constructor
    · intro hinj w hw v hv heq_wv
      dsimp only at heq_wv
      have hP : (φ w).2 + b * (φ w).1 = (φ v).2 + b * (φ v).1 := by
        rw [hrel b w, hrel b v, heq_wv]
      have hw' : φ w ∈ S' := Finset.mem_image_of_mem φ hw
      have hv' : φ v ∈ S' := Finset.mem_image_of_mem φ hv
      have hφeq := hinj hw' hv' hP
      exact hφ hφeq
    · intro hinj P hP Q hQ heq_PQ
      dsimp only at heq_PQ
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hQ
      have hrel_w := hrel b w
      have hrel_v := hrel b v
      have heq' : r * (w.2 + (a0 * b) * w.1) = r * (v.2 + (a0 * b) * v.1) := by
        linear_combination heq_PQ - hrel_w + hrel_v
      have heq'' := hr.mul_left_cancel heq'
      exact congr_arg φ (hinj hw hv heq'')
  have hcard_eq := good_slopes_fiber35_colored_gap_directions_image S S' a0 ha0 hdir
  rw [hcard_eq]
  have hneighbors := good_slopes_fiber35_bad_neighbors S' hcard'
  exact good_slopes_fiber35_anchored_width_gap S' hcard' (u * (q.1 - p.1)) hd h0 h1 hx hline hneighbors
