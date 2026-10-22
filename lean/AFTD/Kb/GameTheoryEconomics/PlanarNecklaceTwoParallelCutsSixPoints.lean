import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsParallelTwoCutConsistent
import AFTD.Kb.GameTheoryEconomics.ThreeSubsetSumTenOrElevenPairBalanced
import AFTD.Kb.Tcs.F

/-!
# planar_necklace_two_parallel_cuts_six_points

Topic: fair_division   Node: ef3edd6ea88d

Provenance: formalization of a published result. Source: arXiv:2610.27956 Theorem 10

Let P be a finite set of 6 points in ℝ × ℝ with a coloring c : (ℝ × ℝ) → Fin 2 having exactly 3 red points (color 0) in P and 3 blue points (color 1) in P. Then there exist a non-zero linear map φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, thresholds t₁, t₂ ∈ ℝ, and an assignment function α : (ℝ × ℝ) → Fin 3 such that is_parallel_two_cut_consistent P φ t₁ t₂ α holds, and for each region i : Fin 3, exactly 1 red point (color 0) and 1 blue point (color 1) of P are assigned to region i by α.
-/

noncomputable def planar_necklace_two_parallel_cuts_six_points_med3 (x y z : ℝ) : ℝ :=
  x + y + z - min (min x y) z - max (max x y) z
lemma planar_necklace_two_parallel_cuts_six_points_med3_neg (x y z : ℝ) :
    planar_necklace_two_parallel_cuts_six_points_med3 (-x) (-y) (-z) =
      - planar_necklace_two_parallel_cuts_six_points_med3 x y z := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_neg_neg, min_neg_neg, max_neg_neg, max_neg_neg]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_xyz {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = y := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_left hxy, min_eq_left (hxy.trans hyz), max_eq_right hxy, max_eq_right hyz]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_xzy {x y z : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = z := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_left (hxz.trans hzy), min_eq_left hxz, max_eq_right (hxz.trans hzy), max_eq_left hzy]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_yxz {x y z : ℝ} (hyx : y ≤ x) (hxz : x ≤ z) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = x := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_right hyx, min_eq_left (hyx.trans hxz), max_eq_left hyx, max_eq_right hxz]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_yzx {x y z : ℝ} (hyz : y ≤ z) (hzx : z ≤ x) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = z := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_right (hyz.trans hzx), min_eq_left hyz, max_eq_left (hyz.trans hzx), max_eq_left hzx]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_zxy {x y z : ℝ} (hzx : z ≤ x) (hxy : x ≤ y) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = x := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_left hxy, min_eq_right hzx, max_eq_right hxy, max_eq_left (hzx.trans hxy)]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_zyx {x y z : ℝ} (hzy : z ≤ y) (hyx : y ≤ x) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = y := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_eq_right hyx, min_eq_right hzy, max_eq_left hyx, max_eq_left (hzy.trans hyx)]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_mem (x y z : ℝ) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = x ∨
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = y ∨
    planar_necklace_two_parallel_cuts_six_points_med3 x y z = z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact Or.inr (Or.inl (planar_necklace_two_parallel_cuts_six_points_med3_xyz hxy hyz))
    · rcases le_total x z with hxz | hzx
      · exact Or.inr (Or.inr (planar_necklace_two_parallel_cuts_six_points_med3_xzy hxz hzy))
      · exact Or.inl (planar_necklace_two_parallel_cuts_six_points_med3_zxy hzx hxy)
  · rcases le_total z x with hzx | hxz
    · rcases le_total y z with hyz | hzy
      · exact Or.inr (Or.inr (planar_necklace_two_parallel_cuts_six_points_med3_yzx hyz hzx))
      · exact Or.inr (Or.inl (planar_necklace_two_parallel_cuts_six_points_med3_zyx hzy hyx))
    · exact Or.inl (planar_necklace_two_parallel_cuts_six_points_med3_yxz hyx hxz)
lemma planar_necklace_two_parallel_cuts_six_points_med3_eq_left {x y z : ℝ}
    (h : planar_necklace_two_parallel_cuts_six_points_med3 x y z = x) :
    (y ≤ x ∧ x ≤ z) ∨ (z ≤ x ∧ x ≤ y) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · rw [planar_necklace_two_parallel_cuts_six_points_med3_xyz hxy hyz] at h
      exact Or.inl ⟨by linarith, by linarith⟩
    · rcases le_total x z with hxz | hzx
      · rw [planar_necklace_two_parallel_cuts_six_points_med3_xzy hxz hzy] at h
        exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨hzx, hxy⟩
  · rcases le_total z x with hzx | hxz
    · rcases le_total y z with hyz | hzy
      · rw [planar_necklace_two_parallel_cuts_six_points_med3_yzx hyz hzx] at h
        exact Or.inl ⟨by linarith, by linarith⟩
      · rw [planar_necklace_two_parallel_cuts_six_points_med3_zyx hzy hyx] at h
        exact Or.inr ⟨hzx, by linarith⟩
    · rw [planar_necklace_two_parallel_cuts_six_points_med3_yxz hyx hxz] at h
      exact Or.inl ⟨hyx, hxz⟩
lemma planar_necklace_two_parallel_cuts_six_points_med3_comm12 (x y z : ℝ) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z =
      planar_necklace_two_parallel_cuts_six_points_med3 y x z := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  rw [min_comm x y, max_comm x y]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_rev (x y z : ℝ) :
    planar_necklace_two_parallel_cuts_six_points_med3 x y z =
      planar_necklace_two_parallel_cuts_six_points_med3 z y x := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
  have h1 : min (min x y) z = min (min z y) x := by
    rw [min_assoc, min_comm x (min y z), min_comm y z]
  have h2 : max (max x y) z = max (max z y) x := by
    rw [max_assoc, max_comm x (max y z), max_comm y z]
  rw [h1,h2]; ring
lemma planar_necklace_two_parallel_cuts_six_points_med3_eq_mid {x y z : ℝ}
    (h : planar_necklace_two_parallel_cuts_six_points_med3 x y z = y) :
    (x ≤ y ∧ y ≤ z) ∨ (z ≤ y ∧ y ≤ x) := by
  have h' : planar_necklace_two_parallel_cuts_six_points_med3 y x z = y := by
    rw [← planar_necklace_two_parallel_cuts_six_points_med3_comm12]; exact h
  exact planar_necklace_two_parallel_cuts_six_points_med3_eq_left h'
lemma planar_necklace_two_parallel_cuts_six_points_med3_eq_right {x y z : ℝ}
    (h : planar_necklace_two_parallel_cuts_six_points_med3 x y z = z) :
    (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) := by
  have h' : planar_necklace_two_parallel_cuts_six_points_med3 z y x = z := by
    rw [← planar_necklace_two_parallel_cuts_six_points_med3_rev]; exact h
  rcases planar_necklace_two_parallel_cuts_six_points_med3_eq_left h' with ⟨a,b⟩ | ⟨a,b⟩
  · exact Or.inr ⟨a,b⟩
  · exact Or.inl ⟨a,b⟩
lemma planar_necklace_two_parallel_cuts_six_points_ordered_triple {α : Type} [DecidableEq α]
    (f : α → ℝ) {p0 p1 p2 : α} (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ({a,b,c} : Finset α) = {p0,p1,p2} ∧
      f a ≤ planar_necklace_two_parallel_cuts_six_points_med3 (f p0) (f p1) (f p2) ∧
      f b = planar_necklace_two_parallel_cuts_six_points_med3 (f p0) (f p1) (f p2) ∧
      planar_necklace_two_parallel_cuts_six_points_med3 (f p0) (f p1) (f p2) ≤ f c := by
  rcases planar_necklace_two_parallel_cuts_six_points_med3_mem (f p0) (f p1) (f p2) with h | h | h
  · rcases planar_necklace_two_parallel_cuts_six_points_med3_eq_left h with ⟨hle,hge⟩ | ⟨hle,hge⟩
    · exact ⟨p1,p0,p2, h01.symm, h12, h02, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
    · exact ⟨p2,p0,p1, h02.symm, h12.symm, h01, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
  · rcases planar_necklace_two_parallel_cuts_six_points_med3_eq_mid h with ⟨hle,hge⟩ | ⟨hle,hge⟩
    · exact ⟨p0,p1,p2, h01, h02, h12, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
    · exact ⟨p2,p1,p0, h12.symm, h02.symm, h01.symm, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
  · rcases planar_necklace_two_parallel_cuts_six_points_med3_eq_right h with ⟨hle,hge⟩ | ⟨hle,hge⟩
    · exact ⟨p0,p2,p1, h02, h01, h12.symm, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
    · exact ⟨p1,p2,p0, h12, h01.symm, h02.symm, by ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc],
        le_trans hle (le_of_eq h.symm), h.symm, le_trans (le_of_eq h) hge⟩
noncomputable def planar_necklace_two_parallel_cuts_six_points_proj (u p : ℝ × ℝ) : ℝ :=
  p.1 * u.1 + p.2 * u.2
lemma planar_necklace_two_parallel_cuts_six_points_proj_neg (u p : ℝ × ℝ) :
    planar_necklace_two_parallel_cuts_six_points_proj (-u) p =
      - planar_necklace_two_parallel_cuts_six_points_proj u p := by
  simp [planar_necklace_two_parallel_cuts_six_points_proj]; ring
lemma planar_necklace_two_parallel_cuts_six_points_continuous_medproj (a b c : ℝ × ℝ) :
    Continuous (fun u : ℝ × ℝ =>
      planar_necklace_two_parallel_cuts_six_points_med3
        (planar_necklace_two_parallel_cuts_six_points_proj u a)
        (planar_necklace_two_parallel_cuts_six_points_proj u b)
        (planar_necklace_two_parallel_cuts_six_points_proj u c)) := by
  unfold planar_necklace_two_parallel_cuts_six_points_med3
    planar_necklace_two_parallel_cuts_six_points_proj
  continuity
lemma planar_necklace_two_parallel_cuts_six_points_medproj_neg (u : ℝ × ℝ) (a b c : ℝ × ℝ) :
    planar_necklace_two_parallel_cuts_six_points_med3
        (planar_necklace_two_parallel_cuts_six_points_proj (-u) a)
        (planar_necklace_two_parallel_cuts_six_points_proj (-u) b)
        (planar_necklace_two_parallel_cuts_six_points_proj (-u) c) =
      - planar_necklace_two_parallel_cuts_six_points_med3
        (planar_necklace_two_parallel_cuts_six_points_proj u a)
        (planar_necklace_two_parallel_cuts_six_points_proj u b)
        (planar_necklace_two_parallel_cuts_six_points_proj u c) := by
  simp only [planar_necklace_two_parallel_cuts_six_points_proj_neg]
  exact planar_necklace_two_parallel_cuts_six_points_med3_neg _ _ _
noncomputable def planar_necklace_two_parallel_cuts_six_points_circ (θ : ℝ) : ℝ × ℝ :=
  (Real.cos θ, Real.sin θ)
lemma planar_necklace_two_parallel_cuts_six_points_exists_median_eq (a0 a1 a2 b0 b1 b2 : ℝ × ℝ) :
    ∃ u : ℝ × ℝ, u ≠ 0 ∧
      planar_necklace_two_parallel_cuts_six_points_med3
          (planar_necklace_two_parallel_cuts_six_points_proj u a0)
          (planar_necklace_two_parallel_cuts_six_points_proj u a1)
          (planar_necklace_two_parallel_cuts_six_points_proj u a2) =
        planar_necklace_two_parallel_cuts_six_points_med3
          (planar_necklace_two_parallel_cuts_six_points_proj u b0)
          (planar_necklace_two_parallel_cuts_six_points_proj u b1)
          (planar_necklace_two_parallel_cuts_six_points_proj u b2) := by
  let F : ℝ × ℝ → ℝ := fun u =>
    planar_necklace_two_parallel_cuts_six_points_med3
        (planar_necklace_two_parallel_cuts_six_points_proj u a0)
        (planar_necklace_two_parallel_cuts_six_points_proj u a1)
        (planar_necklace_two_parallel_cuts_six_points_proj u a2) -
      planar_necklace_two_parallel_cuts_six_points_med3
        (planar_necklace_two_parallel_cuts_six_points_proj u b0)
        (planar_necklace_two_parallel_cuts_six_points_proj u b1)
        (planar_necklace_two_parallel_cuts_six_points_proj u b2)
  have hFcont : Continuous F :=
    (planar_necklace_two_parallel_cuts_six_points_continuous_medproj a0 a1 a2).sub
      (planar_necklace_two_parallel_cuts_six_points_continuous_medproj b0 b1 b2)
  have hFneg : ∀ u, F (-u) = - F u := by
    intro u
    simp only [F, planar_necklace_two_parallel_cuts_six_points_medproj_neg]; ring
  let G : ℝ → ℝ := fun θ => F (planar_necklace_two_parallel_cuts_six_points_circ θ)
  have hGcont : Continuous G :=
    hFcont.comp (by unfold planar_necklace_two_parallel_cuts_six_points_circ; continuity)
  have hGpi : G Real.pi = - G 0 := by
    have hc : planar_necklace_two_parallel_cuts_six_points_circ Real.pi =
        - planar_necklace_two_parallel_cuts_six_points_circ 0 := by
      simp [planar_necklace_two_parallel_cuts_six_points_circ, Real.cos_pi, Real.sin_pi]
    show F (planar_necklace_two_parallel_cuts_six_points_circ Real.pi) =
      - F (planar_necklace_two_parallel_cuts_six_points_circ 0)
    rw [hc, hFneg]
  have hzero : ∃ θ : ℝ, G θ = 0 := by
    rcases le_total (G 0) 0 with hle | hge
    · have hmem : (0:ℝ) ∈ Set.Icc (G 0) (G Real.pi) := by
        rw [Set.mem_Icc]; constructor <;> linarith
      obtain ⟨θ, hθ, hθeq⟩ :=
        intermediate_value_Icc (le_of_lt Real.pi_pos) hGcont.continuousOn hmem
      exact ⟨θ, hθeq⟩
    · have hmem : (0:ℝ) ∈ Set.Icc (G Real.pi) (G 0) := by
        rw [Set.mem_Icc]; constructor <;> linarith
      obtain ⟨θ, hθ, hθeq⟩ :=
        intermediate_value_Icc' (le_of_lt Real.pi_pos) hGcont.continuousOn hmem
      exact ⟨θ, hθeq⟩
  obtain ⟨θ, hθ⟩ := hzero
  refine ⟨planar_necklace_two_parallel_cuts_six_points_circ θ, ?_, ?_⟩
  · intro h
    have hcos : Real.cos θ = 0 := by
      simpa [planar_necklace_two_parallel_cuts_six_points_circ] using congrArg Prod.fst h
    have hsin : Real.sin θ = 0 := by
      simpa [planar_necklace_two_parallel_cuts_six_points_circ] using congrArg Prod.snd h
    have h1 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    rw [hcos, hsin] at h1; norm_num at h1
  · simp only [G, F] at hθ; linarith
lemma planar_necklace_two_parallel_cuts_six_points_filter_three_zero {α : Type} [DecidableEq α]
    (a b c : α) (f : α → Fin 3) (ha : f a = 0) (hb : f b = 1) (hc : f c = 2) :
    ({a,b,c} : Finset α).filter (fun p => f p = 0) = {a} := by
  ext p; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hp⟩
    · rfl
    · rw [hb] at hp; exact absurd hp (by decide)
    · rw [hc] at hp; exact absurd hp (by decide)
  · rintro rfl; exact ⟨Or.inl rfl, ha⟩
lemma planar_necklace_two_parallel_cuts_six_points_filter_three_one {α : Type} [DecidableEq α]
    (a b c : α) (f : α → Fin 3) (ha : f a = 0) (hb : f b = 1) (hc : f c = 2) :
    ({a,b,c} : Finset α).filter (fun p => f p = 1) = {b} := by
  ext p; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hp⟩
    · rw [ha] at hp; exact absurd hp (by decide)
    · rfl
    · rw [hc] at hp; exact absurd hp (by decide)
  · rintro rfl; exact ⟨Or.inr (Or.inl rfl), hb⟩
lemma planar_necklace_two_parallel_cuts_six_points_filter_three_two {α : Type} [DecidableEq α]
    (a b c : α) (f : α → Fin 3) (ha : f a = 0) (hb : f b = 1) (hc : f c = 2) :
    ({a,b,c} : Finset α).filter (fun p => f p = 2) = {c} := by
  ext p; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl, hp⟩
    · rw [ha] at hp; exact absurd hp (by decide)
    · rw [hb] at hp; exact absurd hp (by decide)
    · rfl
  · rintro rfl; exact ⟨Or.inr (Or.inr rfl), hc⟩

/-- For any 6 points in the plane with 3 red and 3 blue, there exist two parallel cuts fairly allocating 1 red and 1 blue point to each of three regions. -/
theorem planar_necklace_two_parallel_cuts_six_points
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2)
    (hP_card : P.card = 6)
    (h_red : (P.filter (fun p => c p = 0)).card = 3)
    (h_blue : (P.filter (fun p => c p = 1)).card = 3) :
    ∃ (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (t₁ t₂ : ℝ) (α : (ℝ × ℝ) → Fin 3),
      φ ≠ 0 ∧
      is_parallel_two_cut_consistent P φ t₁ t₂ α ∧
      ∀ i : Fin 3,
        (P.filter (fun p => α p = i ∧ c p = 0)).card = 1 ∧
        (P.filter (fun p => α p = i ∧ c p = 1)).card = 1 := by
  classical
  rw [Finset.card_eq_three] at h_red
  obtain ⟨r0, r1, r2, hr01, hr02, hr12, hR⟩ := h_red
  rw [Finset.card_eq_three] at h_blue
  obtain ⟨b0, b1, b2, hb01, hb02, hb12, hB⟩ := h_blue
  have hr0R : r0 ∈ P.filter (fun p => c p = 0) := by rw [hR]; simp
  have hr1R : r1 ∈ P.filter (fun p => c p = 0) := by rw [hR]; simp
  have hr2R : r2 ∈ P.filter (fun p => c p = 0) := by rw [hR]; simp
  have hb0B : b0 ∈ P.filter (fun p => c p = 1) := by rw [hB]; simp
  have hb1B : b1 ∈ P.filter (fun p => c p = 1) := by rw [hB]; simp
  have hb2B : b2 ∈ P.filter (fun p => c p = 1) := by rw [hB]; simp
  have hcr0 : c r0 = 0 := (Finset.mem_filter.mp hr0R).2
  have hcr1 : c r1 = 0 := (Finset.mem_filter.mp hr1R).2
  have hcr2 : c r2 = 0 := (Finset.mem_filter.mp hr2R).2
  have hcb0 : c b0 = 1 := (Finset.mem_filter.mp hb0B).2
  have hcb1 : c b1 = 1 := (Finset.mem_filter.mp hb1B).2
  have hcb2 : c b2 = 1 := (Finset.mem_filter.mp hb2B).2
  obtain ⟨u, hu_ne, hu_eq⟩ :=
    planar_necklace_two_parallel_cuts_six_points_exists_median_eq r0 r1 r2 b0 b1 b2
  let φ : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun p => planar_necklace_two_parallel_cuts_six_points_proj u p
      map_add' := by intro a b; simp [planar_necklace_two_parallel_cuts_six_points_proj]; ring
      map_smul' := by intro a b; simp [planar_necklace_two_parallel_cuts_six_points_proj]; ring }
  have hφ : ∀ p, φ p = planar_necklace_two_parallel_cuts_six_points_proj u p := fun p => rfl
  have hs_eq : planar_necklace_two_parallel_cuts_six_points_med3 (φ r0) (φ r1) (φ r2) =
      planar_necklace_two_parallel_cuts_six_points_med3 (φ b0) (φ b1) (φ b2) := by
    simpa [hφ] using hu_eq
  let s : ℝ := planar_necklace_two_parallel_cuts_six_points_med3 (φ r0) (φ r1) (φ r2)
  obtain ⟨rlo, rmid, rhi, hrlo_mid, hrlo_hi, hrmid_hi, hrset, hrle, hrmeq, hrge⟩ :=
    planar_necklace_two_parallel_cuts_six_points_ordered_triple (fun p : ℝ × ℝ => φ p) hr01 hr02 hr12
  obtain ⟨blo, bmid, bhi, hblo_mid, hblo_hi, hbmid_hi, hbset, hble, hbmeq, hbge⟩ :=
    planar_necklace_two_parallel_cuts_six_points_ordered_triple (fun p : ℝ × ℝ => φ p) hb01 hb02 hb12
  have hrmeq' : φ rmid = s := hrmeq
  have hs_eq' : s = planar_necklace_two_parallel_cuts_six_points_med3 (φ b0) (φ b1) (φ b2) := hs_eq
  have hbmeq' : φ bmid = s := by
    show φ bmid = planar_necklace_two_parallel_cuts_six_points_med3 (φ r0) (φ r1) (φ r2)
    rw [hbmeq, hs_eq]
  have hble' : φ blo ≤ s := by rw [hs_eq']; exact hble
  have hbge' : s ≤ φ bhi := by rw [hs_eq']; exact hbge
  have hrloR : rlo ∈ P.filter (fun p => c p = 0) := by
    have h1 : rlo ∈ ({rlo,rmid,rhi} : Finset (ℝ × ℝ)) := by simp
    rw [hrset] at h1
    rwa [← hR] at h1
  have hrmidR : rmid ∈ P.filter (fun p => c p = 0) := by
    have h1 : rmid ∈ ({rlo,rmid,rhi} : Finset (ℝ × ℝ)) := by simp
    rw [hrset] at h1
    rwa [← hR] at h1
  have hrhiR : rhi ∈ P.filter (fun p => c p = 0) := by
    have h1 : rhi ∈ ({rlo,rmid,rhi} : Finset (ℝ × ℝ)) := by simp
    rw [hrset] at h1
    rwa [← hR] at h1
  have hbloB : blo ∈ P.filter (fun p => c p = 1) := by
    have h1 : blo ∈ ({blo,bmid,bhi} : Finset (ℝ × ℝ)) := by simp
    rw [hbset] at h1
    rwa [← hB] at h1
  have hbmidB : bmid ∈ P.filter (fun p => c p = 1) := by
    have h1 : bmid ∈ ({blo,bmid,bhi} : Finset (ℝ × ℝ)) := by simp
    rw [hbset] at h1
    rwa [← hB] at h1
  have hbhiB : bhi ∈ P.filter (fun p => c p = 1) := by
    have h1 : bhi ∈ ({blo,bmid,bhi} : Finset (ℝ × ℝ)) := by simp
    rw [hbset] at h1
    rwa [← hB] at h1
  have hcrlo : c rlo = 0 := (Finset.mem_filter.mp hrloR).2
  have hcrmid : c rmid = 0 := (Finset.mem_filter.mp hrmidR).2
  have hcrhi : c rhi = 0 := (Finset.mem_filter.mp hrhiR).2
  have hcblo : c blo = 1 := (Finset.mem_filter.mp hbloB).2
  have hcbmid : c bmid = 1 := (Finset.mem_filter.mp hbmidB).2
  have hcbhi : c bhi = 1 := (Finset.mem_filter.mp hbhiB).2
  have hne_rb : ∀ (r b : ℝ × ℝ), c r = 0 → c b = 1 → r ≠ b := by
    intro r b hcr hcb h
    rw [h] at hcr
    rw [hcb] at hcr
    exact absurd hcr (by decide)
  let α : (ℝ × ℝ) → Fin 3 := fun p =>
    if p = rlo then 0 else if p = rmid then 1 else if p = rhi then 2
    else if p = blo then 0 else if p = bmid then 1 else if p = bhi then 2 else 0
  have hαrlo : α rlo = 0 := by simp [α]
  have hαrmid : α rmid = 1 := by simp [α, Ne.symm hrlo_mid]
  have hαrhi : α rhi = 2 := by simp [α, Ne.symm hrlo_hi, Ne.symm hrmid_hi]
  have hαblo : α blo = 0 := by
    simp [α, Ne.symm (hne_rb rlo blo hcrlo hcblo), Ne.symm (hne_rb rmid blo hcrmid hcblo),
      Ne.symm (hne_rb rhi blo hcrhi hcblo)]
  have hαbmid : α bmid = 1 := by
    simp [α, Ne.symm (hne_rb rlo bmid hcrlo hcbmid), Ne.symm (hne_rb rmid bmid hcrmid hcbmid),
      Ne.symm (hne_rb rhi bmid hcrhi hcbmid), Ne.symm hblo_mid]
  have hαbhi : α bhi = 2 := by
    simp [α, Ne.symm (hne_rb rlo bhi hcrlo hcbhi), Ne.symm (hne_rb rmid bhi hcrmid hcbhi),
      Ne.symm (hne_rb rhi bhi hcrhi hcbhi), Ne.symm hblo_hi, Ne.symm hbmid_hi]
  have hR' : P.filter (fun p => c p = 0) = ({rlo,rmid,rhi} : Finset (ℝ × ℝ)) := by
    rw [hR]; exact hrset.symm
  have hB' : P.filter (fun p => c p = 1) = ({blo,bmid,bhi} : Finset (ℝ × ℝ)) := by
    rw [hB]; exact hbset.symm
  have hcov : ∀ p ∈ P, p = rlo ∨ p = rmid ∨ p = rhi ∨ p = blo ∨ p = bmid ∨ p = bhi := by
    intro p hp
    have hc2 : ∀ q : Fin 2, q = 0 ∨ q = 1 := by decide
    rcases hc2 (c p) with hc | hc
    · have hmem : p ∈ ({rlo,rmid,rhi} : Finset (ℝ × ℝ)) := by
        rw [← hR']; exact Finset.mem_filter.mpr ⟨hp, hc⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      tauto
    · have hmem : p ∈ ({blo,bmid,bhi} : Finset (ℝ × ℝ)) := by
        rw [← hB']; exact Finset.mem_filter.mpr ⟨hp, hc⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      tauto
  have hcons : ∀ p ∈ P,
      (α p = 0 → φ p ≤ s) ∧ (α p = 1 → s ≤ φ p ∧ φ p ≤ s) ∧ (α p = 2 → s ≤ φ p) := by
    intro p hp
    rcases hcov p hp with h | h | h | h | h | h
    · rw [h, hαrlo]
      exact ⟨fun _ => hrle, fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    · rw [h, hαrmid]
      exact ⟨fun hh => absurd hh (by decide), fun _ => ⟨le_of_eq hrmeq'.symm, le_of_eq hrmeq'⟩, fun hh => absurd hh (by decide)⟩
    · rw [h, hαrhi]
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide), fun _ => hrge⟩
    · rw [h, hαblo]
      exact ⟨fun _ => hble', fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    · rw [h, hαbmid]
      exact ⟨fun hh => absurd hh (by decide), fun _ => ⟨le_of_eq hbmeq'.symm, le_of_eq hbmeq'⟩, fun hh => absurd hh (by decide)⟩
    · rw [h, hαbhi]
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide), fun _ => hbge'⟩
  have hfilterR : ∀ i : Fin 3, P.filter (fun p => α p = i ∧ c p = 0) =
      (P.filter (fun p => c p = 0)).filter (fun p => α p = i) := by
    intro i; ext p; simp only [Finset.mem_filter]; tauto
  have hfilterB : ∀ i : Fin 3, P.filter (fun p => α p = i ∧ c p = 1) =
      (P.filter (fun p => c p = 1)).filter (fun p => α p = i) := by
    intro i; ext p; simp only [Finset.mem_filter]; tauto
  have hRf0 : (P.filter (fun p => c p = 0)).filter (fun p => α p = 0) = {rlo} := by
    rw [hR']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_zero rlo rmid rhi α hαrlo hαrmid hαrhi
  have hRf1 : (P.filter (fun p => c p = 0)).filter (fun p => α p = 1) = {rmid} := by
    rw [hR']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_one rlo rmid rhi α hαrlo hαrmid hαrhi
  have hRf2 : (P.filter (fun p => c p = 0)).filter (fun p => α p = 2) = {rhi} := by
    rw [hR']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_two rlo rmid rhi α hαrlo hαrmid hαrhi
  have hBf0 : (P.filter (fun p => c p = 1)).filter (fun p => α p = 0) = {blo} := by
    rw [hB']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_zero blo bmid bhi α hαblo hαbmid hαbhi
  have hBf1 : (P.filter (fun p => c p = 1)).filter (fun p => α p = 1) = {bmid} := by
    rw [hB']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_one blo bmid bhi α hαblo hαbmid hαbhi
  have hBf2 : (P.filter (fun p => c p = 1)).filter (fun p => α p = 2) = {bhi} := by
    rw [hB']
    exact planar_necklace_two_parallel_cuts_six_points_filter_three_two blo bmid bhi α hαblo hαbmid hαbhi
  have hφne : φ ≠ 0 := by
    intro h0
    have hu : φ u = 0 := by rw [h0]; simp
    have hp : 0 < φ u := by
      rw [hφ]
      have hsq : planar_necklace_two_parallel_cuts_six_points_proj u u = u.1 ^ 2 + u.2 ^ 2 := by
        unfold planar_necklace_two_parallel_cuts_six_points_proj; ring
      rw [hsq]
      rcases eq_or_ne u.1 0 with h1 | h1
      · rcases eq_or_ne u.2 0 with h2 | h2
        · exact absurd (Prod.ext h1 h2) hu_ne
        · nlinarith [sq_pos_of_ne_zero h2]
      · nlinarith [sq_pos_of_ne_zero h1]
    linarith
  refine ⟨φ, s, s, α, hφne, ?_, ?_⟩
  · exact ⟨le_refl s, hcons⟩
  · intro i
    refine ⟨?_, ?_⟩
    · fin_cases i
      · show (P.filter (fun p => α p = (0:Fin 3) ∧ c p = 0)).card = 1
        rw [hfilterR 0, hRf0]; simp
      · show (P.filter (fun p => α p = (1:Fin 3) ∧ c p = 0)).card = 1
        rw [hfilterR 1, hRf1]; simp
      · show (P.filter (fun p => α p = (2:Fin 3) ∧ c p = 0)).card = 1
        rw [hfilterR 2, hRf2]; simp
    · fin_cases i
      · show (P.filter (fun p => α p = (0:Fin 3) ∧ c p = 1)).card = 1
        rw [hfilterB 0, hBf0]; simp
      · show (P.filter (fun p => α p = (1:Fin 3) ∧ c p = 1)).card = 1
        rw [hfilterB 1, hBf1]; simp
      · show (P.filter (fun p => α p = (2:Fin 3) ∧ c p = 1)).card = 1
        rw [hfilterB 2, hBf2]; simp
