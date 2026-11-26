import AFTD.Prelude
import AFTD.Kb.Tcs.Op874CyclePaletteKernel
import AFTD.Kb.Tcs.EqualExternalTripleForcesSharedExposedColor

/-!
# op874_saturated_eight_cycle_forces_high_color_repetition

Topic: graphs   Node: fc1398cfdbaf

Provenance: helper lemma. Local compatibility obstruction in the OP-874 campaign; source problem https://arxiv.org/abs/2610.41950.

For the displayed eight-vertex factor-cycle fragment, with two matching chords and six compatible same-bit interfaces, at least one consecutive pair among the four alternating factor-edge colors is equal. The conclusion requires neither exact matching ownership nor any four-window condition.
-/

def op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4
    (x : Fin 6) (hx : 2 ≤ x.val) : Fin 4 := ⟨x.val - 2, by omega⟩

lemma op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj
    {x y : Fin 6} (hx : 2 ≤ x.val) (hy : 2 ≤ y.val) :
    op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 x hx =
    op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 y hy ↔ x = y := by
  constructor
  · intro h
    ext
    have := congr_arg Fin.val h
    dsimp [op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4] at this
    omega
  · rintro rfl
    rfl

lemma op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
    (inc : Fin 8 → Fin 3 → Fin 14)
    (c : Fin 14 → Fin 6) (h : Fin 8 → Fin 14 → Fin 6)
    (hh_inj : ∀ v : Fin 8, ∀ i j : Fin 3, i ≠ j → h v (inc v i) ≠ h v (inc v j))
    (hh_c_disj : ∀ v : Fin 8, ∀ i j : Fin 3, h v (inc v i) ≠ c (inc v j))
    (u v : Fin 8) (e : Fin 14) (iu1 iu2 iv1 iv2 : Fin 3) (low a b : Fin 6)
    (hcomp : ∀ i j : Fin 3, inc u i ≠ e → inc v j ≠ e → h u (inc u i) ≠ h v (inc v j))
    (he_u1 : inc u iu1 ≠ e) (he_u2 : inc u iu2 ≠ e)
    (he_v1 : inc v iv1 ≠ e) (he_v2 : inc v iv2 ≠ e)
    (hiu : iu1 ≠ iu2) (hiv : iv1 ≠ iv2)
    (hla : low ≠ a) (hlb : low ≠ b) (hab : a ≠ b)
    (hu_low : ∃ i, c (inc u i) = low)
    (hu_a : ∃ i, c (inc u i) = a)
    (hu_b : ∃ i, c (inc u i) = b)
    (hv_low : ∃ i, c (inc v i) = low)
    (hv_a : ∃ i, c (inc v i) = a)
    (hv_b : ∃ i, c (inc v i) = b) : False := by
  rcases hu_low with ⟨iul, heqlu⟩
  rcases hu_a with ⟨iua, heqau⟩
  rcases hu_b with ⟨iub, heqbu⟩
  rcases hv_low with ⟨ivl, heqlv⟩
  rcases hv_a with ⟨iva, heqav⟩
  rcases hv_b with ⟨ivb, heqbv⟩
  have hx : h u (inc u iu1) ≠ low ∧ h u (inc u iu1) ≠ a ∧ h u (inc u iu1) ≠ b := by
    rw [← heqlu, ← heqau, ← heqbu]
    exact ⟨hh_c_disj u iu1 iul, hh_c_disj u iu1 iua, hh_c_disj u iu1 iub⟩
  have hy : h u (inc u iu2) ≠ low ∧ h u (inc u iu2) ≠ a ∧ h u (inc u iu2) ≠ b := by
    rw [← heqlu, ← heqau, ← heqbu]
    exact ⟨hh_c_disj u iu2 iul, hh_c_disj u iu2 iua, hh_c_disj u iu2 iub⟩
  have hu : h v (inc v iv1) ≠ low ∧ h v (inc v iv1) ≠ a ∧ h v (inc v iv1) ≠ b := by
    rw [← heqlv, ← heqav, ← heqbv]
    exact ⟨hh_c_disj v iv1 ivl, hh_c_disj v iv1 iva, hh_c_disj v iv1 ivb⟩
  have hv : h v (inc v iv2) ≠ low ∧ h v (inc v iv2) ≠ a ∧ h v (inc v iv2) ≠ b := by
    rw [← heqlv, ← heqav, ← heqbv]
    exact ⟨hh_c_disj v iv2 ivl, hh_c_disj v iv2 iva, hh_c_disj v iv2 ivb⟩
  have hxy : h u (inc u iu1) ≠ h u (inc u iu2) := hh_inj u iu1 iu2 hiu
  have huv : h v (inc v iv1) ≠ h v (inc v iv2) := hh_inj v iv1 iv2 hiv
  have hshare := equal_external_triple_forces_shared_exposed_color
    low a b (h u (inc u iu1)) (h u (inc u iu2)) (h v (inc v iv1)) (h v (inc v iv2))
    hla hlb hab hx hy hu hv hxy huv
  rcases hshare with h1 | h2 | h3 | h4
  · exact hcomp iu1 iv1 he_u1 he_v1 h1
  · exact hcomp iu1 iv2 he_u1 he_v2 h2
  · exact hcomp iu2 iv1 he_u2 he_v1 h3
  · exact hcomp iu2 iv2 he_u2 he_v2 h4

theorem op874_saturated_eight_cycle_forces_high_color_repetition
    (c : Fin 14 → Fin 6) (h : Fin 8 → Fin 14 → Fin 6) :
    let inc : Fin 8 → Fin 3 → Fin 14 :=
      ![![7,0,8],![0,1,10],![1,2,11],![2,3,9],
        ![3,4,8],![4,5,12],![5,6,13],![6,7,9]]
    let compatible : Fin 8 → Fin 8 → Fin 14 → Prop := fun u v e =>
      ∀ i j : Fin 3, inc u i ≠ e → inc v j ≠ e → h u (inc u i) ≠ h v (inc v j)
    (∀ i : Fin 14, i.val < 8 → 2 ≤ (c i).val) →
    c 8 = 1 → c 9 = 1 → c 10 = 0 → c 11 = 0 → c 12 = 0 → c 13 = 0 →
    (∀ v : Fin 8, ∀ i j : Fin 3, i ≠ j → c (inc v i) ≠ c (inc v j)) →
    (∀ v : Fin 8, ∀ i j : Fin 3, i ≠ j → h v (inc v i) ≠ h v (inc v j)) →
    (∀ v : Fin 8, ∀ i j : Fin 3, h v (inc v i) ≠ c (inc v j)) →
    compatible 0 7 7 → compatible 1 2 1 → compatible 3 4 3 →
    compatible 5 6 5 → compatible 0 4 8 → compatible 3 7 9 →
    c 1 = c 3 ∨ c 3 = c 5 ∨ c 5 = c 7 ∨ c 7 = c 1 := by
  intro inc compatible hc_high hc8 hc9 hc10 hc11 hc12 hc13 hc_inj hh_inj hh_c_disj
    hcomp07 hcomp12 hcomp34 hcomp56 hcomp04 hcomp37
  have h0_ne (i : Fin 14) (hi : i.val < 8) : (0 : Fin 6) ≠ c i := by
    intro h; have := hc_high i hi; rw [← h] at this; revert this; decide
  have h1_ne (i : Fin 14) (hi : i.val < 8) : (1 : Fin 6) ≠ c i := by
    intro h; have := hc_high i hi; rw [← h] at this; revert this; decide
  have h₁ : c 0 ≠ c 7 := hc_inj 0 1 0 (by decide)
  have h₂ : c 0 ≠ c 1 := hc_inj 1 0 1 (by decide)
  have h₃ : c 2 ≠ c 1 := hc_inj 2 1 0 (by decide)
  have h₄ : c 2 ≠ c 3 := hc_inj 3 0 1 (by decide)
  have h₅ : c 4 ≠ c 3 := hc_inj 4 1 0 (by decide)
  have h₆ : c 4 ≠ c 5 := hc_inj 5 0 1 (by decide)
  have h₇ : c 6 ≠ c 5 := hc_inj 6 1 0 (by decide)
  have h₈ : c 6 ≠ c 7 := hc_inj 7 0 1 (by decide)
  have h₉ : c 0 ≠ c 6 := by
    intro heq
    exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
      inc c h hh_inj hh_c_disj 0 7 7 1 2 0 2 1 (c 7) (c 0)
      hcomp07 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (h1_ne 7 (by decide)) (h1_ne 0 (by decide)) (hc_inj 0 0 1 (by decide))
      ⟨2, hc8⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, hc9⟩ ⟨1, rfl⟩ ⟨0, heq.symm⟩
  have h₁₀ : c 2 ≠ c 4 := by
    intro heq
    exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
      inc c h hh_inj hh_c_disj 3 4 3 0 2 1 2 1 (c 3) (c 2)
      hcomp34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (h1_ne 3 (by decide)) (h1_ne 2 (by decide)) (hc_inj 3 1 0 (by decide))
      ⟨2, hc9⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨2, hc8⟩ ⟨0, rfl⟩ ⟨1, heq.symm⟩
  have h₁₁ : c 0 ≠ c 2 := by
    intro heq
    exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
      inc c h hh_inj hh_c_disj 1 2 1 0 2 1 2 0 (c 1) (c 0)
      hcomp12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (h0_ne 1 (by decide)) (h0_ne 0 (by decide)) (hc_inj 1 1 0 (by decide))
      ⟨2, hc10⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨2, hc11⟩ ⟨0, rfl⟩ ⟨1, heq.symm⟩
  have h₁₂ : c 4 ≠ c 6 := by
    intro heq
    exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
      inc c h hh_inj hh_c_disj 5 6 5 0 2 1 2 0 (c 5) (c 4)
      hcomp56 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (h0_ne 5 (by decide)) (h0_ne 4 (by decide)) (hc_inj 5 1 0 (by decide))
      ⟨2, hc12⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨2, hc13⟩ ⟨0, rfl⟩ ⟨1, heq.symm⟩
  have hp : ¬ ((c 7 = c 3 ∧ c 0 = c 4) ∨ (c 7 = c 4 ∧ c 0 = c 3)) := by
    intro hor
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
        inc c h hh_inj hh_c_disj 0 4 8 0 1 0 1 1 (c 7) (c 0)
        hcomp04 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (h1_ne 7 (by decide)) (h1_ne 0 (by decide)) (hc_inj 0 0 1 (by decide))
        ⟨2, hc8⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, hc8⟩ ⟨0, h1.symm⟩ ⟨1, h2.symm⟩
    · exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
        inc c h hh_inj hh_c_disj 0 4 8 0 1 0 1 1 (c 7) (c 0)
        hcomp04 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (h1_ne 7 (by decide)) (h1_ne 0 (by decide)) (hc_inj 0 0 1 (by decide))
        ⟨2, hc8⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, hc8⟩ ⟨1, h1.symm⟩ ⟨0, h2.symm⟩
  have hq : ¬ ((c 7 = c 3 ∧ c 6 = c 2) ∨ (c 7 = c 2 ∧ c 6 = c 3)) := by
    intro hor
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
        inc c h hh_inj hh_c_disj 3 7 9 0 1 0 1 1 (c 3) (c 2)
        hcomp37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (h1_ne 3 (by decide)) (h1_ne 2 (by decide)) (hc_inj 3 1 0 (by decide))
        ⟨2, hc9⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨2, hc9⟩ ⟨1, h1⟩ ⟨0, h2⟩
    · exact op874_saturated_eight_cycle_forces_high_color_repetition_no_same_external_triple
        inc c h hh_inj hh_c_disj 3 7 9 0 1 0 1 1 (c 3) (c 2)
        hcomp37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (h1_ne 3 (by decide)) (h1_ne 2 (by decide)) (hc_inj 3 1 0 (by decide))
        ⟨2, hc9⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨2, hc9⟩ ⟨0, h2⟩ ⟨1, h1⟩
  have H0 := hc_high 0 (by decide)
  have H1 := hc_high 1 (by decide)
  have H2 := hc_high 2 (by decide)
  have H3 := hc_high 3 (by decide)
  have H4 := hc_high 4 (by decide)
  have H5 := hc_high 5 (by decide)
  have H6 := hc_high 6 (by decide)
  have H7 := hc_high 7 (by decide)
  let a := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 0) H0
  let x := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 1) H1
  let c_ := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 2) H2
  let t := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 3) H3
  let d := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 4) H4
  let y := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 5) H5
  let b := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 6) H6
  let s := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4 (c 7) H7
  have inj07 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H7
  have inj01 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H1
  have inj21 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H2 H1
  have inj23 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H2 H3
  have inj43 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H4 H3
  have inj45 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H4 H5
  have inj65 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H6 H5
  have inj67 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H6 H7
  have inj06 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H6
  have inj24 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H2 H4
  have inj02 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H2
  have inj46 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H4 H6
  have inj73 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H7 H3
  have inj04 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H4
  have inj74 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H7 H4
  have inj03 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H0 H3
  have inj62 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H6 H2
  have inj72 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H7 H2
  have inj63 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H6 H3
  have inj13 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H1 H3
  have inj35 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H3 H5
  have inj57 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H5 H7
  have inj71 := op874_saturated_eight_cycle_forces_high_color_repetition_to_fin4_inj H7 H1
  have k1 : a ≠ s := by intro h; exact h₁ (inj07.mp h)
  have k2 : a ≠ x := by intro h; exact h₂ (inj01.mp h)
  have k3 : c_ ≠ x := by intro h; exact h₃ (inj21.mp h)
  have k4 : c_ ≠ t := by intro h; exact h₄ (inj23.mp h)
  have k5 : d ≠ t := by intro h; exact h₅ (inj43.mp h)
  have k6 : d ≠ y := by intro h; exact h₆ (inj45.mp h)
  have k7 : b ≠ y := by intro h; exact h₇ (inj65.mp h)
  have k8 : b ≠ s := by intro h; exact h₈ (inj67.mp h)
  have k9 : a ≠ b := by intro h; exact h₉ (inj06.mp h)
  have k10 : c_ ≠ d := by intro h; exact h₁₀ (inj24.mp h)
  have k11 : a ≠ c_ := by intro h; exact h₁₁ (inj02.mp h)
  have k12 : d ≠ b := by intro h; exact h₁₂ (inj46.mp h)
  have kp : ¬ ((s = t ∧ a = d) ∨ (s = d ∧ a = t)) := by
    intro hor
    apply hp
    rcases hor with ⟨hs, ha⟩ | ⟨hs, ha⟩
    · exact Or.inl ⟨inj73.mp hs, inj04.mp ha⟩
    · exact Or.inr ⟨inj74.mp hs, inj03.mp ha⟩
  have kq : ¬ ((s = t ∧ b = c_) ∨ (s = c_ ∧ b = t)) := by
    intro hor
    apply hq
    rcases hor with ⟨hs, hb⟩ | ⟨hs, hb⟩
    · exact Or.inl ⟨inj73.mp hs, inj62.mp hb⟩
    · exact Or.inr ⟨inj72.mp hs, inj63.mp hb⟩
  have res := op874_cycle_palette_kernel a x c_ t d y b s k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 kp kq
  rcases res with h | h | h | h
  · exact Or.inl (inj13.mp h)
  · exact Or.inr (Or.inl (inj35.mp h))
  · exact Or.inr (Or.inr (Or.inl (inj57.mp h)))
  · exact Or.inr (Or.inr (Or.inr (inj71.mp h)))
