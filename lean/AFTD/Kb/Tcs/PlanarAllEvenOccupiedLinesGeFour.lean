import AFTD.Prelude
import AFTD.Kb.Tcs.PlanarAllEven
import AFTD.Kb.Tcs.PlanarOccupiedLines

/-!
# planar_all_even_occupied_lines_ge_four

Topic: combinatorics   Node: 1f703f33d100

Provenance: formalization of a published result. Source: arXiv:2610.38864 Lemma 7.2: All-even sets in ℝ² and ℝ³

For every planar all-even set A and every non-zero vector u, the number of lines perpendicular to u meeting A is at least 4.
-/

def planar_all_even_occupied_lines_ge_four_zrot (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-u 1, u 0]

lemma planar_all_even_occupied_lines_ge_four_inner_u (p u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ p u = p 0 * u 0 + p 1 * u 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma planar_all_even_occupied_lines_ge_four_inner_zrot (p u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ p (planar_all_even_occupied_lines_ge_four_zrot u) = p 0 * (-u 1) + p 1 * u 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, planar_all_even_occupied_lines_ge_four_zrot, mul_comm]

lemma planar_all_even_occupied_lines_ge_four_inner_u_self_ne_zero (u : EuclideanSpace ℝ (Fin 2))
    (hu : u ≠ 0) : u 0 * u 0 + u 1 * u 1 ≠ 0 := by
  intro h
  apply hu
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  ext i
  fin_cases i <;> simp [h0, h1]

lemma planar_all_even_occupied_lines_ge_four_pair_inj (u : EuclideanSpace ℝ (Fin 2)) (hu : u ≠ 0)
    (p q : EuclideanSpace ℝ (Fin 2))
    (hf : inner ℝ p u = inner ℝ q u)
    (hg : inner ℝ p (planar_all_even_occupied_lines_ge_four_zrot u) =
          inner ℝ q (planar_all_even_occupied_lines_ge_four_zrot u)) : p = q := by
  rw [planar_all_even_occupied_lines_ge_four_inner_u p u,
      planar_all_even_occupied_lines_ge_four_inner_u q u] at hf
  rw [planar_all_even_occupied_lines_ge_four_inner_zrot p u,
      planar_all_even_occupied_lines_ge_four_inner_zrot q u] at hg
  have hkey := planar_all_even_occupied_lines_ge_four_inner_u_self_ne_zero u hu
  have h0 : p 0 - q 0 = 0 := by
    have h : (p 0 - q 0) * (u 0 * u 0 + u 1 * u 1) = 0 := by
      linear_combination (u 0) * hf - (u 1) * hg
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · exact absurd h' hkey
  have h1 : p 1 - q 1 = 0 := by
    have h : (p 1 - q 1) * (u 0 * u 0 + u 1 * u 1) = 0 := by
      linear_combination (u 1) * hf + (u 0) * hg
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · exact absurd h' hkey
  ext i
  fin_cases i <;> simp <;> linarith

lemma planar_all_even_occupied_lines_ge_four_inner_zrot_self (u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (planar_all_even_occupied_lines_ge_four_zrot u)
      (planar_all_even_occupied_lines_ge_four_zrot u) = u 0 * u 0 + u 1 * u 1 := by
  rw [planar_all_even_occupied_lines_ge_four_inner_zrot]
  simp [planar_all_even_occupied_lines_ge_four_zrot]
  ring

lemma planar_all_even_occupied_lines_ge_four_inner_u_zrot (u : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ u (planar_all_even_occupied_lines_ge_four_zrot u) = 0 := by
  rw [planar_all_even_occupied_lines_ge_four_inner_u]
  simp [planar_all_even_occupied_lines_ge_four_zrot]
  ring

lemma planar_all_even_occupied_lines_ge_four_zrot_ne_zero (u : EuclideanSpace ℝ (Fin 2))
    (hu : u ≠ 0) : planar_all_even_occupied_lines_ge_four_zrot u ≠ 0 := by
  intro h
  have hS := planar_all_even_occupied_lines_ge_four_inner_zrot_self u
  rw [h] at hS
  simp at hS
  exact planar_all_even_occupied_lines_ge_four_inner_u_self_ne_zero u hu hS.symm

lemma planar_all_even_occupied_lines_ge_four_vs_ne_zero (u : EuclideanSpace ℝ (Fin 2))
    (hu : u ≠ 0) (s : ℝ) : u + s • planar_all_even_occupied_lines_ge_four_zrot u ≠ 0 := by
  intro h
  have hz := planar_all_even_occupied_lines_ge_four_inner_zrot_self u
  have hk := planar_all_even_occupied_lines_ge_four_inner_u_self_ne_zero u hu
  have h1 : inner ℝ (u + s • planar_all_even_occupied_lines_ge_four_zrot u)
      (planar_all_even_occupied_lines_ge_four_zrot u) = s * (u 0 * u 0 + u 1 * u 1) := by
    rw [inner_add_left, inner_smul_left,
      planar_all_even_occupied_lines_ge_four_inner_u_zrot, hz]
    simp
  rw [h] at h1
  rw [inner_zero_left] at h1
  have hs : s = 0 := by
    rcases mul_eq_zero.mp h1.symm with h' | h'
    · exact h'
    · exact absurd h' hk
  rw [hs, zero_smul, add_zero] at h
  exact hu h

lemma planar_all_even_occupied_lines_ge_four_inner_vs (p u : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    inner ℝ p (u + s • planar_all_even_occupied_lines_ge_four_zrot u) =
      inner ℝ p u + s * inner ℝ p (planar_all_even_occupied_lines_ge_four_zrot u) := by
  rw [inner_add_right, inner_smul_right]

lemma planar_all_even_occupied_lines_ge_four_core {α : Type*} [DecidableEq α]
    (A : Finset α) (f g : α → ℝ) (c1 c2 : ℝ)
    (hne : A.Nonempty) (hc : c1 ≠ c2)
    (himg : A.image f = {c1, c2})
    (hinj : ∀ p ∈ A, ∀ q ∈ A, f p = f q → g p = g q → p = q)
    (heven : ∀ s : ℝ, Even ((A.image (fun p => f p + s * g p)).card))
    (hevenG : Even ((A.image g).card)) : False := by
  classical
  have hc1mem : c1 ∈ A.image f := by rw [himg]; simp
  have hc2mem : c2 ∈ A.image f := by rw [himg]; simp
  obtain ⟨p1, hp1A, hp1f⟩ := Finset.mem_image.mp hc1mem
  obtain ⟨p2, hp2A, hp2f⟩ := Finset.mem_image.mp hc2mem
  set A1 : Finset α := A.filter (fun p => f p = c1) with hA1
  set A2 : Finset α := A.filter (fun p => f p = c2) with hA2
  have hA1ne : A1.Nonempty := ⟨p1, by rw [hA1]; exact Finset.mem_filter.mpr ⟨hp1A, hp1f⟩⟩
  have hA2ne : A2.Nonempty := ⟨p2, by rw [hA2]; exact Finset.mem_filter.mpr ⟨hp2A, hp2f⟩⟩
  have hmem : ∀ p ∈ A, p ∈ A1 ∨ p ∈ A2 := by
    intro p hp
    have hthis : f p ∈ A.image f := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [himg, Finset.mem_insert, Finset.mem_singleton] at hthis
    rcases hthis with h | h
    · left; rw [hA1]; exact Finset.mem_filter.mpr ⟨hp, h⟩
    · right; rw [hA2]; exact Finset.mem_filter.mpr ⟨hp, h⟩
  have hfA1 : ∀ p ∈ A1, f p = c1 := fun p hp => by
    rw [hA1] at hp; exact (Finset.mem_filter.mp hp).2
  have hfA2 : ∀ p ∈ A2, f p = c2 := fun p hp => by
    rw [hA2] at hp; exact (Finset.mem_filter.mp hp).2
  have hA1sub : ∀ p ∈ A1, p ∈ A := fun p hp => by
    rw [hA1] at hp; exact (Finset.mem_filter.mp hp).1
  have hA2sub : ∀ p ∈ A2, p ∈ A := fun p hp => by
    rw [hA2] at hp; exact (Finset.mem_filter.mp hp).1
  have hg_inj_A1 : ∀ p ∈ A1, ∀ q ∈ A1, g p = g q → p = q := by
    intro p hp q hq hgpq
    exact hinj p (hA1sub p hp) q (hA1sub q hq) (by rw [hfA1 p hp, hfA1 q hq]) hgpq
  have hg_inj_A2 : ∀ p ∈ A2, ∀ q ∈ A2, g p = g q → p = q := by
    intro p hp q hq hgpq
    exact hinj p (hA2sub p hp) q (hA2sub q hq) (by rw [hfA2 p hp, hfA2 q hq]) hgpq
  have hwithin1 : ∀ s : ℝ, s ≠ 0 → ∀ p ∈ A1, ∀ q ∈ A1,
      f p + s * g p = f q + s * g q → p = q := by
    intro s hs p hp q hq heq
    have hf : f p = f q := by rw [hfA1 p hp, hfA1 q hq]
    have hgs : s * g p = s * g q := by linarith
    exact hg_inj_A1 p hp q hq (mul_left_cancel₀ hs hgs)
  have hwithin2 : ∀ s : ℝ, s ≠ 0 → ∀ p ∈ A2, ∀ q ∈ A2,
      f p + s * g p = f q + s * g q → p = q := by
    intro s hs p hp q hq heq
    have hf : f p = f q := by rw [hfA2 p hp, hfA2 q hq]
    have hgs : s * g p = s * g q := by linarith
    exact hg_inj_A2 p hp q hq (mul_left_cancel₀ hs hgs)
  have hEvenA : Even A.card := by
    set Bad : Finset ℝ := (A1 ×ˢ A2).image (fun q => (c2 - c1) / (g q.1 - g q.2)) with hBad
    set s1 : ℝ := ((∑ x ∈ Bad, x ^ 2) + 1) with hs1
    have hs1pos : 0 < s1 := by
      rw [hs1]
      have hnn : 0 ≤ ∑ x ∈ Bad, x ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg i)
      linarith
    have hs1ne : s1 ≠ 0 := ne_of_gt hs1pos
    have hs1gt : ∀ x ∈ Bad, x < s1 := by
      intro x hx
      have hle : x ^ 2 ≤ ∑ y ∈ Bad, y ^ 2 := Finset.single_le_sum (fun i _ => sq_nonneg i) hx
      rw [hs1]
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hs1notin : s1 ∉ Bad := by
      intro h
      have := hs1gt s1 h
      linarith
    have hno_cross : ∀ p ∈ A1, ∀ q ∈ A2, f p + s1 * g p ≠ f q + s1 * g q := by
      intro p hp q hq heq
      have hfp : f p = c1 := hfA1 p hp
      have hfq : f q = c2 := hfA2 q hq
      have hkey : s1 * (g p - g q) = c2 - c1 := by
        rw [mul_sub]; linarith
      by_cases hgg : g p - g q = 0
      · have hgg' : g p = g q := by linarith
        rw [hgg'] at heq
        exact hc (by linarith)
      · have hbad : (c2 - c1) / (g p - g q) ∈ Bad := by
          rw [hBad]
          exact Finset.mem_image.mpr ⟨(p, q), by rw [Finset.mem_product]; exact ⟨hp, hq⟩, rfl⟩
        have hval : s1 = (c2 - c1) / (g p - g q) := by
          rw [eq_div_iff hgg]
          exact hkey
        rw [← hval] at hbad
        exact hs1notin hbad
    have hall_inj : ∀ p ∈ A, ∀ q ∈ A, f p + s1 * g p = f q + s1 * g q → p = q := by
      intro p hp q hq heq
      rcases hmem p hp with hp1 | hp2
      · rcases hmem q hq with hq1 | hq2
        · exact hwithin1 s1 hs1ne p hp1 q hq1 heq
        · exact absurd heq (hno_cross p hp1 q hq2)
      · rcases hmem q hq with hq1 | hq2
        · exact absurd heq.symm (hno_cross q hq1 p hp2)
        · exact hwithin2 s1 hs1ne p hp2 q hq2 heq
    have hcard1 : (A.image (fun p => f p + s1 * g p)).card = A.card := by
      rw [Finset.card_image_iff]
      intro p hp q hq heq
      exact hall_inj p hp q hq heq
    have hev := heven s1
    rwa [hcard1] at hev
  obtain ⟨p1min, hp1minA1, hp1min_le⟩ := Finset.exists_min_image A1 g hA1ne
  obtain ⟨p2max, hp2maxA2, hp2max_ge⟩ := Finset.exists_max_image A2 g hA2ne
  obtain ⟨p1max, hp1maxA1, hp1max_ge⟩ := Finset.exists_max_image A1 g hA1ne
  obtain ⟨p2min, hp2minA2, hp2min_le⟩ := Finset.exists_min_image A2 g hA2ne
  have hmax_eq : ∀ p ∈ A1, ∀ q ∈ A2,
      (g q - g p = g p2max - g p1min ↔ p = p1min ∧ q = p2max) := by
    intro p hp q hq
    constructor
    · intro heq
      have h1 := hp1min_le p hp
      have h2 := hp2max_ge q hq
      have hgp : g p = g p1min := by linarith
      have hgq : g q = g p2max := by linarith
      exact ⟨hg_inj_A1 p hp p1min hp1minA1 hgp, hg_inj_A2 q hq p2max hp2maxA2 hgq⟩
    · intro ⟨hp', hq'⟩; rw [hp', hq']
  have hmin_eq : ∀ p ∈ A1, ∀ q ∈ A2,
      (g q - g p = g p2min - g p1max ↔ p = p1max ∧ q = p2min) := by
    intro p hp q hq
    constructor
    · intro heq
      have h1 := hp1max_ge p hp
      have h2 := hp2min_le q hq
      have hgp : g p = g p1max := by linarith
      have hgq : g q = g p2min := by linarith
      exact ⟨hg_inj_A1 p hp p1max hp1maxA1 hgp, hg_inj_A2 q hq p2min hp2minA2 hgq⟩
    · intro ⟨hp', hq'⟩; rw [hp', hq']
  have hcoinc : ∃ (s : ℝ) (pa pb : α), s ≠ 0 ∧ pa ∈ A1 ∧ pb ∈ A2 ∧
      f pa + s * g pa = f pb + s * g pb ∧
      (∀ p ∈ A1, ∀ q ∈ A2, f p + s * g p = f q + s * g q → p = pa ∧ q = pb) := by
    by_cases hM : g p2max - g p1min ≠ 0
    · refine ⟨(c1 - c2) / (g p2max - g p1min), p1min, p2max,
        div_ne_zero (sub_ne_zero.mpr hc) hM, hp1minA1, hp2maxA2, ?_, ?_⟩
      · have hsM : (c1 - c2) / (g p2max - g p1min) * (g p2max - g p1min) = c1 - c2 :=
          div_mul_cancel₀ (c1 - c2) hM
        have h2 : (c1 - c2) / (g p2max - g p1min) * g p2max
            - (c1 - c2) / (g p2max - g p1min) * g p1min = c1 - c2 := by
          rw [← mul_sub]; exact hsM
        rw [hfA1 p1min hp1minA1, hfA2 p2max hp2maxA2]
        linarith
      · intro p hp q hq heq
        have hsne : (c1 - c2) / (g p2max - g p1min) ≠ 0 :=
          div_ne_zero (sub_ne_zero.mpr hc) hM
        have hsM : (c1 - c2) / (g p2max - g p1min) * (g p2max - g p1min) = c1 - c2 :=
          div_mul_cancel₀ (c1 - c2) hM
        have h2 : (c1 - c2) / (g p2max - g p1min) * g p2max
            - (c1 - c2) / (g p2max - g p1min) * g p1min = c1 - c2 := by
          rw [← mul_sub]; exact hsM
        rw [hfA1 p hp, hfA2 q hq] at heq
        have hlin : (c1 - c2) / (g p2max - g p1min) * g q
            - (c1 - c2) / (g p2max - g p1min) * g p = c1 - c2 := by linarith
        have h3 : g q - g p = g p2max - g p1min := by
          have hEq : (c1 - c2) / (g p2max - g p1min) * (g q - g p)
              = (c1 - c2) / (g p2max - g p1min) * (g p2max - g p1min) := by
            rw [mul_sub, mul_sub]; linarith
          exact mul_left_cancel₀ hsne hEq
        exact (hmax_eq p hp q hq).mp h3
    · have hM0 : g p2max - g p1min = 0 := not_not.mp hM
      by_cases hm : g p2min - g p1max ≠ 0
      · refine ⟨(c1 - c2) / (g p2min - g p1max), p1max, p2min,
          div_ne_zero (sub_ne_zero.mpr hc) hm, hp1maxA1, hp2minA2, ?_, ?_⟩
        · have hsM : (c1 - c2) / (g p2min - g p1max) * (g p2min - g p1max) = c1 - c2 :=
            div_mul_cancel₀ (c1 - c2) hm
          have h2 : (c1 - c2) / (g p2min - g p1max) * g p2min
              - (c1 - c2) / (g p2min - g p1max) * g p1max = c1 - c2 := by
            rw [← mul_sub]; exact hsM
          rw [hfA1 p1max hp1maxA1, hfA2 p2min hp2minA2]
          linarith
        · intro p hp q hq heq
          have hsne : (c1 - c2) / (g p2min - g p1max) ≠ 0 :=
            div_ne_zero (sub_ne_zero.mpr hc) hm
          have hsM : (c1 - c2) / (g p2min - g p1max) * (g p2min - g p1max) = c1 - c2 :=
            div_mul_cancel₀ (c1 - c2) hm
          have h2 : (c1 - c2) / (g p2min - g p1max) * g p2min
              - (c1 - c2) / (g p2min - g p1max) * g p1max = c1 - c2 := by
            rw [← mul_sub]; exact hsM
          rw [hfA1 p hp, hfA2 q hq] at heq
          have hlin : (c1 - c2) / (g p2min - g p1max) * g q
              - (c1 - c2) / (g p2min - g p1max) * g p = c1 - c2 := by linarith
          have h3 : g q - g p = g p2min - g p1max := by
            have hEq : (c1 - c2) / (g p2min - g p1max) * (g q - g p)
                = (c1 - c2) / (g p2min - g p1max) * (g p2min - g p1max) := by
              rw [mul_sub, mul_sub]; linarith
            exact mul_left_cancel₀ hsne hEq
          exact (hmin_eq p hp q hq).mp h3
      · exfalso
        have hm0 : g p2min - g p1max = 0 := not_not.mp hm
        have hconst : ∀ p ∈ A, g p = g p1min := by
          intro p hp
          rcases hmem p hp with hp1 | hp2
          · have h1 := hp1min_le p hp1
            have h2 := hp1max_ge p hp1
            have hle : g p2min ≤ g p2max := hp2min_le p2max hp2maxA2
            linarith
          · have h1 := hp2min_le p hp2
            have h2 := hp2max_ge p hp2
            have hle1 : g p1min ≤ g p1max := hp1min_le p1max hp1maxA1
            have hle : g p2min ≤ g p2max := hp2min_le p2max hp2maxA2
            linarith
        have hsing : A.image g = {g p1min} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          constructor
          · exact Finset.mem_image.mpr ⟨p1min, hA1sub p1min hp1minA1, rfl⟩
          · intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨p, hp, rfl⟩ := hx
            exact hconst p hp
        have hcardg : (A.image g).card = 1 := by rw [hsing]; simp
        rw [hcardg] at hevenG
        obtain ⟨k, hk⟩ := hevenG
        omega
  obtain ⟨s, pa, pb, hsne, hpa1, hpb2, hcoin, huniq⟩ := hcoinc
  have hpaA : pa ∈ A := hA1sub pa hpa1
  have hpbA : pb ∈ A := hA2sub pb hpb2
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact hc (by rw [← hfA1 p hp1, ← hfA2 p hp2])
  have hpa_ne_pb : pa ≠ pb := by
    intro h
    rw [h] at hpa1
    exact (Finset.disjoint_left.mp hdisj) hpa1 hpb2
  have hsub_erase : (A.erase pb).image (fun p => f p + s * g p)
      = A.image (fun p => f p + s * g p) := by
    apply Finset.Subset.antisymm
    · intro v hv
      rw [Finset.mem_image] at hv ⊢
      obtain ⟨p, hp, rfl⟩ := hv
      rw [Finset.mem_erase] at hp
      exact ⟨p, hp.2, rfl⟩
    · intro v hv
      rw [Finset.mem_image] at hv ⊢
      obtain ⟨p, hpA, rfl⟩ := hv
      by_cases hpb : p = pb
      · refine ⟨pa, ?_, ?_⟩
        · rw [Finset.mem_erase]; exact ⟨hpa_ne_pb, hpaA⟩
        · rw [hpb]; exact hcoin
      · refine ⟨p, ?_, rfl⟩
        · rw [Finset.mem_erase]; exact ⟨hpb, hpA⟩
  have hinj_erase : Set.InjOn (fun p => f p + s * g p) ↑(A.erase pb) := by
    intro p hp q hq heq
    rw [Finset.mem_coe, Finset.mem_erase] at hp hq
    rcases hmem p hp.2 with hp1 | hp2
    · rcases hmem q hq.2 with hq1 | hq2
      · exact hwithin1 s hsne p hp1 q hq1 heq
      · exact absurd (huniq p hp1 q hq2 heq).2 hq.1
    · rcases hmem q hq.2 with hq1 | hq2
      · exact absurd (huniq q hq1 p hp2 heq.symm).2 hp.1
      · exact hwithin2 s hsne p hp2 q hq2 heq
  have hcard_erase : (A.image (fun p => f p + s * g p)).card = (A.erase pb).card := by
    rw [← hsub_erase, Finset.card_image_iff]
    exact hinj_erase
  have hcard_erase2 : (A.erase pb).card = A.card - 1 := Finset.card_erase_of_mem hpbA
  have hEven_sub : Even (A.card - 1) := by
    have hev := heven s
    rw [hcard_erase, hcard_erase2] at hev
    exact hev
  obtain ⟨k, hk⟩ := hEvenA
  obtain ⟨j, hj⟩ := hEven_sub
  have hpos : 0 < A.card := Finset.card_pos.mpr hne
  omega

/-- Lemma 7.2 of arXiv:2610.38864: every planar all-even set meets at least 4 lines in every direction. -/
theorem planar_all_even_occupied_lines_ge_four
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hA : planar_all_even A)
    (u : EuclideanSpace ℝ (Fin 2)) (hu : u ≠ 0) :
    4 ≤ planar_occupied_lines A u := by
  classical
  set z := planar_all_even_occupied_lines_ge_four_zrot u with hzdef
  have hzne : z ≠ 0 := planar_all_even_occupied_lines_ge_four_zrot_ne_zero u hu
  have hn2 : planar_occupied_lines A u ≠ 2 := by
    intro hn
    obtain ⟨c1, c2, hc, himg⟩ := Finset.card_eq_two.mp hn
    have hinj : ∀ p ∈ A, ∀ q ∈ A, inner ℝ p u = inner ℝ q u →
        inner ℝ p z = inner ℝ q z → p = q := by
      intro p _ q _ hf hg
      exact planar_all_even_occupied_lines_ge_four_pair_inj u hu p q hf (by simpa [hzdef] using hg)
    have heven : ∀ s : ℝ,
        Even ((A.image (fun p => inner ℝ p u + s * inner ℝ p z)).card) := by
      intro s
      have hfun : (fun p => inner ℝ p u + s * inner ℝ p z)
          = (fun p => inner ℝ p (u + s • z)) := by
        funext p
        rw [hzdef]
        exact (planar_all_even_occupied_lines_ge_four_inner_vs p u s).symm
      rw [hfun]
      have hh := hA.2 (u + s • z) (by rw [hzdef]; exact planar_all_even_occupied_lines_ge_four_vs_ne_zero u hu s)
      simpa [planar_occupied_lines] using hh
    have hevenG : Even ((A.image (fun p => inner ℝ p z)).card) := by
      have hh := hA.2 z hzne
      simpa [planar_occupied_lines] using hh
    exact planar_all_even_occupied_lines_ge_four_core A (fun p => inner ℝ p u)
      (fun p => inner ℝ p z) c1 c2 hA.1 hc himg hinj heven hevenG
  have hEvenU : Even (planar_occupied_lines A u) := hA.2 u hu
  have hpos : 0 < planar_occupied_lines A u := by
    rw [planar_occupied_lines]
    exact Finset.card_pos.mpr (hA.1.image _)
  obtain ⟨k, hk⟩ := hEvenU
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hk; omega
    · exact h
  have hkne1 : k ≠ 1 := by
    intro h
    apply hn2
    rw [hk, h]
  have hk2 : 2 ≤ k := by omega
  rw [hk]; omega
