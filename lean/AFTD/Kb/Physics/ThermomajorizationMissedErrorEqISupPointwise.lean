import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationMissedError
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_missed_error_eq_iSup_pointwise

Topic: quantum_mechanics   Node: f0dd75053d3c

Provenance: helper lemma. arXiv:2610.35433, Population capacity and the geometry of thermomajorization

For any dimension n ≥ 2 and probe set F ⊆ {1,...,n-1} such that the set of unprobed ranks {1,...,n-1} \ F is nonempty, the conversion missed error thermomajorization_missed_error n F equals the supremum over all unprobed ranks j ∈ {1,...,n-1} \ F of the pointwise missed error thermomajorization_pointwise_missed_error n F j.
-/

private lemma tmeip_ax_const_mem (n : ℕ) (hn : 1 ≤ n) :
    (fun _ : Fin n => (n : ℝ)⁻¹) ∈ stdSimplex ℝ (Fin n) ∧
      Antitone (fun _ : Fin n => (n : ℝ)⁻¹) := by
  constructor
  · constructor
    · intro i; exact inv_nonneg.mpr (Nat.cast_nonneg n)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
  · exact antitone_const

private lemma tmeip_ax_probe_self (n : ℕ) (G : Finset ℕ) (s : Fin n → ℝ) :
    thermomajorization_probe_error n G s s = 0 := by
  unfold thermomajorization_probe_error
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact le_refl 0
    · rw [Finset.mem_image] at hz
      obtain ⟨j, _, hj⟩ := hz
      rw [← hj]; simp [thermomajorization_diff]
  · exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

private lemma tmeip_ax_probe_nonneg (n : ℕ) (G : Finset ℕ) (x y : Fin n → ℝ) :
    0 ≤ thermomajorization_probe_error n G x y := by
  unfold thermomajorization_probe_error
  exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

private lemma tmeip_ax_diff_le_probe (n : ℕ) (G : Finset ℕ) (x y : Fin n → ℝ) (j : ℕ)
    (hj : j ∈ G) :
    thermomajorization_diff x y j ≤ thermomajorization_probe_error n G x y := by
  unfold thermomajorization_probe_error
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))

private lemma tmeip_ax_diff_le_one (n : ℕ) (x y : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hy : y ∈ stdSimplex ℝ (Fin n)) (j : ℕ) :
    thermomajorization_diff x y j ≤ 1 := by
  rw [show thermomajorization_diff x y j =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i:ℕ) < j), (y i - x i) from by
    unfold thermomajorization_diff; rfl]
  have hx0 : ∀ i, 0 ≤ x i := hx.1
  have hy0 : ∀ i, 0 ≤ y i := hy.1
  have hysum : ∑ i : Fin n, y i = 1 := hy.2
  have h1 : ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i:ℕ) < j), (y i - x i)
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i:ℕ) < j), y i := by
    apply Finset.sum_le_sum; intro i hi
    have hxi : 0 ≤ x i := hx0 i; linarith
  have h2 : ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i:ℕ) < j), y i
      ≤ ∑ i : Fin n, y i := by
    apply Finset.sum_le_univ_sum_of_nonneg; intro i; exact hy0 i
  linarith

private lemma tmeip_ax_probe_le_one (n : ℕ) (G : Finset ℕ) (x y : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) (hy : y ∈ stdSimplex ℝ (Fin n)) :
    thermomajorization_probe_error n G x y ≤ 1 := by
  apply Finset.max'_le
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · norm_num
  · rw [Finset.mem_image] at hz
    obtain ⟨j, _, rfl⟩ := hz
    exact tmeip_ax_diff_le_one n x y hx hy j

private lemma tmeip_ax_A_le_one (n : ℕ) (I F : Finset ℕ) {x y : Fin n → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin n) ∧ Antitone x)
    (hy : y ∈ stdSimplex ℝ (Fin n) ∧ Antitone y) :
    thermomajorization_probe_error n I x y - thermomajorization_probe_error n F x y ≤ 1 := by
  have h1 := tmeip_ax_probe_le_one n I x y hx.1 hy.1
  have h2 := tmeip_ax_probe_nonneg n F x y
  linarith

private lemma tmeip_ax_B_le_one (n : ℕ) (F : Finset ℕ) (j : ℕ) {x y : Fin n → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin n) ∧ Antitone x)
    (hy : y ∈ stdSimplex ℝ (Fin n) ∧ Antitone y) :
    thermomajorization_diff x y j - thermomajorization_probe_error n F x y ≤ 1 := by
  have h1 := tmeip_ax_diff_le_one n x y hx.1 hy.1 j
  have h2 := tmeip_ax_probe_nonneg n F x y
  linarith

private lemma tmeip_ax_exists_max (n : ℕ) (G : Finset ℕ) (x y : Fin n → ℝ)
    (h : 0 < thermomajorization_probe_error n G x y) :
    ∃ j ∈ G, thermomajorization_diff x y j = thermomajorization_probe_error n G x y := by
  have hmem : thermomajorization_probe_error n G x y ∈
      insert 0 (Finset.image (thermomajorization_diff x y) G) := by
    unfold thermomajorization_probe_error
    exact Finset.max'_mem _ _
  rw [Finset.mem_insert] at hmem
  rcases hmem with h0 | himg
  · rw [h0] at h; exact absurd h (lt_irrefl 0)
  · rw [Finset.mem_image] at himg
    exact himg

private lemma tmeip_ax_bdd1 {n : ℕ} {P : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {S : Set (Fin n → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b, a ∈ S → b ∈ S → P a b ≤ c) (x : Fin n → ℝ) (hx : x ∈ S) :
    BddAbove (Set.range fun y : Fin n → ℝ => ⨆ (_ : y ∈ S), P x y) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_cases hy : y ∈ S
  · simp only [ciSup_pos hy]; exact h x y hx hy
  · haveI : IsEmpty (y ∈ S) := ⟨fun hh => hy hh⟩
    simp only [Real.iSup_of_isEmpty]; exact hc

private lemma tmeip_ax_bdd2 {n : ℕ} {P : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {S : Set (Fin n → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b, a ∈ S → b ∈ S → P a b ≤ c) :
    BddAbove (Set.range fun x : Fin n → ℝ =>
      ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ciSup_pos hx]
    refine Real.iSup_le (fun y => ?_) hc
    by_cases hy : y ∈ S
    · simp only [ciSup_pos hy]; exact h x y hx hy
    · haveI : IsEmpty (y ∈ S) := ⟨fun hh => hy hh⟩
      simp only [Real.iSup_of_isEmpty]; exact hc
  · haveI : IsEmpty (x ∈ S) := ⟨fun hh => hx hh⟩
    simp only [Real.iSup_of_isEmpty]; exact hc

private lemma tmeip_ax_iSup2_le {n : ℕ} {P : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {S : Set (Fin n → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b, a ∈ S → b ∈ S → P a b ≤ c) :
    (⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y) ≤ c := by
  refine Real.iSup_le (fun x => ?_) hc
  by_cases hx : x ∈ S
  · simp only [ciSup_pos hx]
    refine Real.iSup_le (fun y => ?_) hc
    by_cases hy : y ∈ S
    · simp only [ciSup_pos hy]; exact h x y hx hy
    · haveI : IsEmpty (y ∈ S) := ⟨fun hh => hy hh⟩
      simp only [Real.iSup_of_isEmpty]; exact hc
  · haveI : IsEmpty (x ∈ S) := ⟨fun hh => hx hh⟩
    simp only [Real.iSup_of_isEmpty]; exact hc

private lemma tmeip_ax_le2 {n : ℕ} {P : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {S : Set (Fin n → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a b, a ∈ S → b ∈ S → P a b ≤ c)
    (x y : Fin n → ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    P x y ≤ ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y := by
  have h1 : BddAbove (Set.range fun y : Fin n → ℝ => ⨆ (_ : y ∈ S), P x y) :=
    tmeip_ax_bdd1 hc h x hx
  have h2 : BddAbove (Set.range fun x : Fin n → ℝ =>
      ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y) := tmeip_ax_bdd2 hc h
  have e1 : (⨆ (_ : y ∈ S), P x y) = P x y := ciSup_pos hy
  have e2 : (⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y)
      = ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y := ciSup_pos hx
  calc P x y = ⨆ (_ : y ∈ S), P x y := e1.symm
    _ ≤ ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y := le_ciSup h1 y
    _ = ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y := e2.symm
    _ ≤ ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), P x y := le_ciSup h2 x

private lemma tmeip_ax_iSup3_le {J : Finset ℕ} {G : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, j ∈ J → G j ≤ c) :
    (⨆ j : ℕ, ⨆ (_ : j ∈ J), G j) ≤ c := by
  refine Real.iSup_le (fun j => ?_) hc
  by_cases hj : j ∈ J
  · simp only [ciSup_pos hj]; exact h j hj
  · haveI : IsEmpty (j ∈ J) := ⟨fun hh => hj hh⟩
    simp only [Real.iSup_of_isEmpty]; exact hc

private lemma tmeip_ax_sup4_nonneg {n : ℕ} {S : Set (Fin n → ℝ)}
    {P : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ a b, a ∈ S → b ∈ S → P a b ≤ c)
    (u : Fin n → ℝ) (hu : u ∈ S) (h : 0 ≤ P u u) :
    0 ≤ ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ, ⨆ (_ : b ∈ S), P a b :=
  h.trans (tmeip_ax_le2 hc hb u u hu hu)

private lemma tmeip_ax_le6 {n : ℕ} {J : Finset ℕ} {S : Set (Fin n → ℝ)}
    {B : ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ j a b, j ∈ J → a ∈ S → b ∈ S → B j a b ≤ c)
    (j : ℕ) (hj : j ∈ J) (a b : Fin n → ℝ) (ha : a ∈ S) (hb' : b ∈ S) :
    B j a b ≤ ⨆ j : ℕ, ⨆ (_ : j ∈ J), ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S),
      ⨆ b : Fin n → ℝ, ⨆ (_ : b ∈ S), B j a b := by
  have hbJ : BddAbove (Set.range fun j' : ℕ => ⨆ (_ : j' ∈ J), ⨆ a : Fin n → ℝ,
      ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ, ⨆ (_ : b ∈ S), B j' a b) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨j', rfl⟩
    by_cases hj' : j' ∈ J
    · simp only [ciSup_pos hj']
      exact tmeip_ax_iSup2_le (S := S) hc (fun a b ha hb' => hb j' a b hj' ha hb')
    · haveI : IsEmpty (j' ∈ J) := ⟨fun hh => hj' hh⟩
      simp only [Real.iSup_of_isEmpty]; exact hc
  have e : (⨆ (_ : j ∈ J), ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ,
      ⨆ (_ : b ∈ S), B j a b) = ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ,
      ⨆ (_ : b ∈ S), B j a b := ciSup_pos hj
  calc B j a b
      ≤ ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ, ⨆ (_ : b ∈ S), B j a b :=
        tmeip_ax_le2 (S := S) hc (fun a b ha hb' => hb j a b hj ha hb') a b ha hb'
    _ = ⨆ (_ : j ∈ J), ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S), ⨆ b : Fin n → ℝ,
        ⨆ (_ : b ∈ S), B j a b := e.symm
    _ ≤ ⨆ j : ℕ, ⨆ (_ : j ∈ J), ⨆ a : Fin n → ℝ, ⨆ (_ : a ∈ S),
        ⨆ b : Fin n → ℝ, ⨆ (_ : b ∈ S), B j a b := le_ciSup hbJ j

/-- The global thermomajorization missed error equals the supremum of pointwise missed errors over all unprobed ranks. -/
theorem thermomajorization_missed_error_eq_iSup_pointwise
    (n : ℕ) (hn : 2 ≤ n) (F : Finset ℕ) (hF : F ⊆ Finset.Ioo 0 n)
    (hF_ne : (Finset.Ioo 0 n \ F).Nonempty) :
    thermomajorization_missed_error n F =
      ⨆ j ∈ Finset.Ioo 0 n \ F, thermomajorization_pointwise_missed_error n F j := by
  unfold thermomajorization_missed_error thermomajorization_pointwise_missed_error
  set S : Set (Fin n → ℝ) := {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} with hS
  set I : Finset ℕ := Finset.Ioo 0 n with hI
  set J : Finset ℕ := I \ F with hJ
  have hmemS : ∀ v : Fin n → ℝ, (v ∈ S ↔ v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v) := by
    intro v; rw [hS]; rfl
  have hu : (fun _ : Fin n => (n : ℝ)⁻¹) ∈ S :=
    (hmemS _).mpr (tmeip_ax_const_mem n (by omega))
  have hJne : J.Nonempty := by rw [hJ, hI]; exact hF_ne
  have hcA : ∀ a b : Fin n → ℝ, a ∈ S → b ∈ S →
      thermomajorization_probe_error n I a b - thermomajorization_probe_error n F a b ≤ 1 :=
    fun a b ha hb => tmeip_ax_A_le_one n I F ((hmemS a).mp ha) ((hmemS b).mp hb)
  have hcB : ∀ (k : ℕ) (a b : Fin n → ℝ), k ∈ J → a ∈ S → b ∈ S →
      thermomajorization_diff a b k - thermomajorization_probe_error n F a b ≤ 1 :=
    fun k a b _ ha hb => tmeip_ax_B_le_one n F k ((hmemS a).mp ha) ((hmemS b).mp hb)
  have huI : thermomajorization_probe_error n I (fun _ : Fin n => (n:ℝ)⁻¹)
      (fun _ : Fin n => (n:ℝ)⁻¹) = 0 := tmeip_ax_probe_self n I _
  have huF : thermomajorization_probe_error n F (fun _ : Fin n => (n:ℝ)⁻¹)
      (fun _ : Fin n => (n:ℝ)⁻¹) = 0 := tmeip_ax_probe_self n F _
  have hM_nonneg : 0 ≤ ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ,
      ⨆ (_ : y ∈ S), (thermomajorization_probe_error n I x y -
        thermomajorization_probe_error n F x y) := by
    refine tmeip_ax_sup4_nonneg (S := S) (c := 1) zero_le_one hcA _ hu ?_
    rw [huI, huF]; norm_num
  obtain ⟨j₀, hj₀⟩ := hJne
  have hP_nonneg : 0 ≤ ⨆ k : ℕ, ⨆ (_ : k ∈ J), ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S),
      ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), (thermomajorization_diff x y k -
        thermomajorization_probe_error n F x y) := by
    have h := tmeip_ax_le6 (J := J) (S := S) (c := 1) zero_le_one hcB j₀ hj₀
      (fun _ : Fin n => (n:ℝ)⁻¹) (fun _ : Fin n => (n:ℝ)⁻¹) hu hu
    have hz : thermomajorization_diff (fun _ : Fin n => (n:ℝ)⁻¹) (fun _ : Fin n => (n:ℝ)⁻¹) j₀
        - thermomajorization_probe_error n F (fun _ : Fin n => (n:ℝ)⁻¹)
          (fun _ : Fin n => (n:ℝ)⁻¹) = 0 := by
      rw [huF]; simp [thermomajorization_diff]
    linarith
  apply le_antisymm
  · refine tmeip_ax_iSup2_le (S := S) (c := ⨆ k : ℕ, ⨆ (_ : k ∈ J), ⨆ x : Fin n → ℝ,
      ⨆ (_ : x ∈ S), ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), (thermomajorization_diff x y k -
        thermomajorization_probe_error n F x y)) hP_nonneg ?_
    intro x y hx hy
    by_cases hpos : 0 < thermomajorization_probe_error n I x y
    · obtain ⟨k, hkI, hke⟩ := tmeip_ax_exists_max n I x y hpos
      by_cases hkF : k ∈ F
      · have h1 : thermomajorization_diff x y k ≤ thermomajorization_probe_error n F x y :=
          tmeip_ax_diff_le_probe n F x y k hkF
        have h2 : thermomajorization_probe_error n I x y - thermomajorization_probe_error n F x y
            ≤ 0 := by rw [← hke]; linarith
        linarith
      · have hkJ : k ∈ J := by rw [hJ]; exact Finset.mem_sdiff.mpr ⟨hkI, hkF⟩
        have he : thermomajorization_probe_error n I x y - thermomajorization_probe_error n F x y
            = thermomajorization_diff x y k - thermomajorization_probe_error n F x y := by
          rw [← hke]
        rw [he]
        exact tmeip_ax_le6 (J := J) (S := S) (c := 1) zero_le_one hcB k hkJ x y hx hy
    · push_neg at hpos
      have h0 : thermomajorization_probe_error n I x y = 0 :=
        le_antisymm hpos (tmeip_ax_probe_nonneg n I x y)
      rw [h0]
      linarith [tmeip_ax_probe_nonneg n F x y]
  · refine tmeip_ax_iSup3_le (J := J) (c := ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S),
      ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), (thermomajorization_probe_error n I x y -
        thermomajorization_probe_error n F x y)) hM_nonneg ?_
    intro k hk
    have hkI : k ∈ I := (Finset.mem_sdiff.mp (by rw [← hJ]; exact hk)).1
    refine tmeip_ax_iSup2_le (S := S) (c := ⨆ x : Fin n → ℝ, ⨆ (_ : x ∈ S),
      ⨆ y : Fin n → ℝ, ⨆ (_ : y ∈ S), (thermomajorization_probe_error n I x y -
        thermomajorization_probe_error n F x y)) hM_nonneg ?_
    intro x y hx hy
    have h1 : thermomajorization_diff x y k ≤ thermomajorization_probe_error n I x y :=
      tmeip_ax_diff_le_probe n I x y k hkI
    have h2 : thermomajorization_diff x y k - thermomajorization_probe_error n F x y
        ≤ thermomajorization_probe_error n I x y - thermomajorization_probe_error n F x y := by
      linarith
    exact h2.trans (tmeip_ax_le2 (S := S) (c := 1) zero_le_one hcA x y hx hy)
