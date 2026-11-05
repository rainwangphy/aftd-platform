import AFTD.Prelude
import AFTD.Kb.Tcs.IsIsotropicPosition
import AFTD.Kb.Tcs.SumRangeSqAddGe
import AFTD.Kb.Tcs.IsotropicChainCubicIneq

/-!
# isotropic_intersection_size_bound

Topic: combinatorics   Node: 8f845abcca75

Provenance: formalization of a published result. Source: arXiv:2611.04644 Lemma A.4 -- Additive energy, Freiman's lemma, and an edge-isoperimetric problem on the boolean cube

Let A ⊂ ℝ^d be a finite, non-empty set in isotropic position (so that ∑_{a ∈ A} a = 0 and ∑_{a ∈ A} (a · u)^2 = |A| ‖u‖^2 for all u ∈ ℝ^d), and let v ∈ ℝ^d be non-zero. Then |A ∩ (v + A)| ≤ 2|A| / ‖v‖^2.
-/

open scoped Pointwise

section IsotropicIntersectionBoundHelpers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq V]

/-- Distributing a difference of scalar multiples. -/
lemma isotropic_intersection_size_bound_sub_smul_sub (a v : V) (r s : ℝ) :
    a - r • v - s • v = a - (r + s) • v := by
  rw [add_smul]; abel

/-- Multiples of a nonzero vector by distinct naturals are distinct. -/
lemma isotropic_intersection_size_bound_nat_smul_inj {v : V} (hv : v ≠ 0) {i j : ℕ}
    (h : (i : ℝ) • v = (j : ℝ) • v) : i = j := by
  have h3 : (((i : ℝ)) - ((j : ℝ))) • v = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr h
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have h5 : (i : ℝ) = (j : ℝ) := by linarith
    exact Nat.cast_injective h5
  · exact absurd h4 hv

/-- Walking backwards along `v` from a point of a finite set eventually leaves it. -/
lemma isotropic_intersection_size_bound_back_exists (A : Finset V) (v : V) (hv : v ≠ 0)
    (a : V) (ha : a ∈ A) : ∃ k : ℕ, a - ((k : ℝ) + 1) • v ∉ A := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hinj : Function.Injective (fun k : ℕ => a - ((k : ℝ) + 1) • v) := by
    intro k l hkl
    have hkl' : a - ((k : ℝ) + 1) • v = a - ((l : ℝ) + 1) • v := hkl
    have h1 : -(((k : ℝ) + 1) • v) = -(((l : ℝ) + 1) • v) := by
      rw [sub_eq_add_neg, sub_eq_add_neg] at hkl'
      exact add_left_cancel hkl'
    have h2 : ((k : ℝ) + 1) • v = ((l : ℝ) + 1) • v := neg_injective h1
    have h3 : (((k : ℝ) + 1) - ((l : ℝ) + 1)) • v = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h2
    rcases smul_eq_zero.mp h3 with h4 | h4
    · have h5 : (k : ℝ) = (l : ℝ) := by linarith
      exact Nat.cast_injective h5
    · exact absurd h4 hv
  have hsub : Set.range (fun k : ℕ => a - ((k : ℝ) + 1) • v) ⊆ (A : Set V) := by
    rintro x ⟨k, rfl⟩
    exact hcon k
  exact (Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)) A.finite_toSet

/-- The number of backward steps along `v` from a point before leaving `A`. -/
noncomputable def isotropic_intersection_size_bound_chainK (A : Finset V) (v : V) (a : V) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, a - ((k : ℝ) + 1) • v ∉ A then Nat.find h else 0

/-- The first point of the `v`-chain through `a`. -/
noncomputable def isotropic_intersection_size_bound_chainRep (A : Finset V) (v : V) (a : V) : V := by
  classical
  exact a - (isotropic_intersection_size_bound_chainK A v a : ℝ) • v

/-- The `v`-chain of `A` starting at `r`. -/
noncomputable def isotropic_intersection_size_bound_chain (A : Finset V) (v : V) (r : V) : Finset V := by
  classical
  exact A.filter (fun b => isotropic_intersection_size_bound_chainRep A v b = r)

/-- The index of the top point of the chain starting at `r`. -/
noncomputable def isotropic_intersection_size_bound_chainLen (A : Finset V) (v : V) (r : V) : ℕ :=
  (isotropic_intersection_size_bound_chain A v r).sup (isotropic_intersection_size_bound_chainK A v)

/-- The set of chain starts of `A` in direction `v`. -/
noncomputable def isotropic_intersection_size_bound_chainStarts (A : Finset V) (v : V) : Finset V := by
  classical
  exact A.image (isotropic_intersection_size_bound_chainRep A v)

variable (A : Finset V) (v : V)

lemma isotropic_intersection_size_bound_mem_chain {r b : V} :
    b ∈ isotropic_intersection_size_bound_chain A v r ↔
      b ∈ A ∧ isotropic_intersection_size_bound_chainRep A v b = r := by
  classical
  simp [isotropic_intersection_size_bound_chain]

lemma isotropic_intersection_size_bound_chainK_spec (hv : v ≠ 0) (a : V) (ha : a ∈ A) :
    a - ((isotropic_intersection_size_bound_chainK A v a : ℝ) + 1) • v ∉ A := by
  classical
  have h := isotropic_intersection_size_bound_back_exists A v hv a ha
  have hfind : isotropic_intersection_size_bound_chainK A v a = Nat.find h := dif_pos h
  rw [hfind]
  exact Nat.find_spec h

lemma isotropic_intersection_size_bound_chainK_min (hv : v ≠ 0) {a : V} (ha : a ∈ A) {j : ℕ}
    (hj : j < isotropic_intersection_size_bound_chainK A v a) :
    a - ((j : ℝ) + 1) • v ∈ A := by
  classical
  by_contra hmem
  have h := isotropic_intersection_size_bound_back_exists A v hv a ha
  have hfind : isotropic_intersection_size_bound_chainK A v a = Nat.find h := dif_pos h
  exact (Nat.find_min h (hfind ▸ hj)) hmem

lemma isotropic_intersection_size_bound_chainK_le (hv : v ≠ 0) {a : V} (ha : a ∈ A) {j : ℕ}
    (hj : a - ((j : ℝ) + 1) • v ∉ A) : isotropic_intersection_size_bound_chainK A v a ≤ j := by
  classical
  have h := isotropic_intersection_size_bound_back_exists A v hv a ha
  have hfind : isotropic_intersection_size_bound_chainK A v a = Nat.find h := dif_pos h
  rw [hfind]
  exact Nat.find_min' h hj

lemma isotropic_intersection_size_bound_mem_of_le (hv : v ≠ 0) {a : V} (ha : a ∈ A) :
    ∀ l : ℕ, l ≤ isotropic_intersection_size_bound_chainK A v a → a - (l : ℝ) • v ∈ A := by
  intro l hl
  match l with
  | 0 => simpa using ha
  | (j + 1) =>
      have hlt : j < isotropic_intersection_size_bound_chainK A v a := by omega
      have hmem := isotropic_intersection_size_bound_chainK_min A v hv ha hlt
      simpa [Nat.cast_add, Nat.cast_one] using hmem

lemma isotropic_intersection_size_bound_chainRep_eq_add (a : V) :
    isotropic_intersection_size_bound_chainRep A v a
      + (isotropic_intersection_size_bound_chainK A v a : ℝ) • v = a := by
  simp [isotropic_intersection_size_bound_chainRep, sub_add_cancel]

lemma isotropic_intersection_size_bound_chainRep_mem (hv : v ≠ 0) {a : V} (ha : a ∈ A) :
    isotropic_intersection_size_bound_chainRep A v a ∈ A := by
  have h := isotropic_intersection_size_bound_mem_of_le A v hv ha
    (isotropic_intersection_size_bound_chainK A v a) le_rfl
  rw [isotropic_intersection_size_bound_chainRep]
  exact h

lemma isotropic_intersection_size_bound_chainRep_sub_v (hv : v ≠ 0) {a : V} (ha : a ∈ A) :
    isotropic_intersection_size_bound_chainRep A v a - v ∉ A := by
  have h := isotropic_intersection_size_bound_chainK_spec A v hv a ha
  have hEq : isotropic_intersection_size_bound_chainRep A v a - v
      = a - ((isotropic_intersection_size_bound_chainK A v a : ℝ) + 1) • v := by
    rw [isotropic_intersection_size_bound_chainRep, add_smul, one_smul]
    abel
  rwa [hEq]

lemma isotropic_intersection_size_bound_chainK_index (hv : v ≠ 0) {a : V} (ha : a ∈ A) {l : ℕ}
    (hl : l ≤ isotropic_intersection_size_bound_chainK A v a) :
    isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v)
      = isotropic_intersection_size_bound_chainK A v a - l := by
  classical
  have hmem : a - (l : ℝ) • v ∈ A := isotropic_intersection_size_bound_mem_of_le A v hv ha l hl
  have hupper : isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v)
      ≤ isotropic_intersection_size_bound_chainK A v a - l := by
    apply isotropic_intersection_size_bound_chainK_le A v hv hmem
    have hs : ((l : ℝ) + (((isotropic_intersection_size_bound_chainK A v a - l : ℕ) : ℝ) + 1))
        = ((isotropic_intersection_size_bound_chainK A v a : ℝ) + 1) := by
      rw [Nat.cast_sub hl]; ring
    have hEq : a - (l : ℝ) • v
        - (((isotropic_intersection_size_bound_chainK A v a - l : ℕ) : ℝ) + 1) • v
        = a - ((isotropic_intersection_size_bound_chainK A v a : ℝ) + 1) • v := by
      rw [isotropic_intersection_size_bound_sub_smul_sub, hs]
    rw [hEq]
    exact isotropic_intersection_size_bound_chainK_spec A v hv a ha
  have hlower : isotropic_intersection_size_bound_chainK A v a - l
      ≤ isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have hnotmem : a - (l : ℝ) • v
        - ((isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) : ℝ) + 1) • v ∉ A :=
      isotropic_intersection_size_bound_chainK_spec A v hv (a - (l : ℝ) • v) hmem
    apply hnotmem
    have hEq : a - (l : ℝ) • v
        - ((isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) : ℝ) + 1) • v
        = a - ((l + isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) + 1 : ℕ) : ℝ) • v := by
      have hs : ((l : ℝ) + ((isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) : ℝ) + 1))
          = ((l + isotropic_intersection_size_bound_chainK A v (a - (l : ℝ) • v) + 1 : ℕ) : ℝ) := by
        push_cast; ring
      rw [isotropic_intersection_size_bound_sub_smul_sub, hs]
    rw [hEq]
    exact isotropic_intersection_size_bound_mem_of_le A v hv ha _ (by omega)
  exact le_antisymm hupper hlower

lemma isotropic_intersection_size_bound_chainRep_index (hv : v ≠ 0) {a : V} (ha : a ∈ A) {l : ℕ}
    (hl : l ≤ isotropic_intersection_size_bound_chainK A v a) :
    isotropic_intersection_size_bound_chainRep A v (a - (l : ℝ) • v)
      = isotropic_intersection_size_bound_chainRep A v a := by
  have hh := isotropic_intersection_size_bound_chainK_index A v hv ha hl
  simp only [isotropic_intersection_size_bound_chainRep, hh]
  have hs : ((l : ℝ) + (((isotropic_intersection_size_bound_chainK A v a) - l : ℕ) : ℝ))
      = (isotropic_intersection_size_bound_chainK A v a : ℝ) := by
    rw [Nat.cast_sub hl]; ring
  rw [isotropic_intersection_size_bound_sub_smul_sub, hs]

lemma isotropic_intersection_size_bound_chainK_chainRep (hv : v ≠ 0) {a : V} (ha : a ∈ A) :
    isotropic_intersection_size_bound_chainK A v
      (isotropic_intersection_size_bound_chainRep A v a) = 0 := by
  have h := isotropic_intersection_size_bound_chainK_index A v hv ha
    (l := isotropic_intersection_size_bound_chainK A v a) le_rfl
  have hEq : isotropic_intersection_size_bound_chainRep A v a
      = a - (isotropic_intersection_size_bound_chainK A v a : ℝ) • v := rfl
  rw [hEq, h, Nat.sub_self]

lemma isotropic_intersection_size_bound_chainRep_fix (hv : v ≠ 0) {a : V} (ha : a ∈ A) :
    isotropic_intersection_size_bound_chainRep A v (isotropic_intersection_size_bound_chainRep A v a)
      = isotropic_intersection_size_bound_chainRep A v a := by
  have h := isotropic_intersection_size_bound_chainRep_index A v hv ha
    (l := isotropic_intersection_size_bound_chainK A v a) le_rfl
  have hEq : isotropic_intersection_size_bound_chainRep A v a
      = a - (isotropic_intersection_size_bound_chainK A v a : ℝ) • v := rfl
  rw [hEq] at h
  exact h

/-- The chain starting at `r` is the affine progression `r + i • v`, `i ≤ chainLen`. -/
lemma isotropic_intersection_size_bound_chain_image {r : V} (hv : v ≠ 0) (hr : r ∈ A)
    (hfix : isotropic_intersection_size_bound_chainRep A v r = r) :
    isotropic_intersection_size_bound_chain A v r
      = (Finset.range (isotropic_intersection_size_bound_chainLen A v r + 1)).image
        (fun i : ℕ => r + (i : ℝ) • v) := by
  classical
  have hne : (isotropic_intersection_size_bound_chain A v r).Nonempty :=
    ⟨r, (isotropic_intersection_size_bound_mem_chain A v).mpr ⟨hr, hfix⟩⟩
  ext b
  constructor
  · intro hb
    obtain ⟨hbA, hbr⟩ := (isotropic_intersection_size_bound_mem_chain A v).mp hb
    have hle : isotropic_intersection_size_bound_chainK A v b
        ≤ isotropic_intersection_size_bound_chainLen A v r := by
      simpa [isotropic_intersection_size_bound_chainLen] using
        Finset.le_sup (f := isotropic_intersection_size_bound_chainK A v) hb
    refine Finset.mem_image.mpr ⟨isotropic_intersection_size_bound_chainK A v b,
      Finset.mem_range.mpr (by omega), ?_⟩
    have h := isotropic_intersection_size_bound_chainRep_eq_add A v b
    rw [hbr] at h
    exact h
  · intro hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_range] at hi
    obtain ⟨c, hc, hcm⟩ := Finset.exists_mem_eq_sup (isotropic_intersection_size_bound_chain A v r)
      hne (isotropic_intersection_size_bound_chainK A v)
    obtain ⟨hcA, hcr⟩ := (isotropic_intersection_size_bound_mem_chain A v).mp hc
    have hcm' : isotropic_intersection_size_bound_chainK A v c
        = isotropic_intersection_size_bound_chainLen A v r := hcm.symm
    have hile : i ≤ isotropic_intersection_size_bound_chainLen A v r := by omega
    have hmemc : c - ((isotropic_intersection_size_bound_chainLen A v r - i : ℕ) : ℝ) • v ∈ A :=
      isotropic_intersection_size_bound_mem_of_le A v hv hcA _ (by omega)
    have hrep : isotropic_intersection_size_bound_chainRep A v
        (c - ((isotropic_intersection_size_bound_chainLen A v r - i : ℕ) : ℝ) • v) = r := by
      rw [isotropic_intersection_size_bound_chainRep_index A v hv hcA
        (l := isotropic_intersection_size_bound_chainLen A v r - i) (by omega), hcr]
    have hceq : c = r + (isotropic_intersection_size_bound_chainLen A v r : ℝ) • v := by
      have h := isotropic_intersection_size_bound_chainRep_eq_add A v c
      rw [hcr, hcm'] at h
      exact h.symm
    have heq : r + (i : ℝ) • v
        = c - ((isotropic_intersection_size_bound_chainLen A v r - i : ℕ) : ℝ) • v := by
      rw [hceq]
      have hsc : ((isotropic_intersection_size_bound_chainLen A v r : ℝ)
          - ((isotropic_intersection_size_bound_chainLen A v r - i : ℕ) : ℝ)) = (i : ℝ) := by
        rw [Nat.cast_sub hile]; ring
      rw [← hsc, sub_smul]
      abel
    rw [heq]
    exact (isotropic_intersection_size_bound_mem_chain A v).mpr ⟨hmemc, hrep⟩

lemma isotropic_intersection_size_bound_chain_inj (hv : v ≠ 0) {r : V} :
    Set.InjOn (fun i : ℕ => r + (i : ℝ) • v)
      ↑(Finset.range (isotropic_intersection_size_bound_chainLen A v r + 1)) := by
  intro i _ j _ hij
  exact isotropic_intersection_size_bound_nat_smul_inj hv (add_left_cancel hij)

lemma isotropic_intersection_size_bound_chain_card {r : V} (hv : v ≠ 0) (hr : r ∈ A)
    (hfix : isotropic_intersection_size_bound_chainRep A v r = r) :
    (isotropic_intersection_size_bound_chain A v r).card
      = isotropic_intersection_size_bound_chainLen A v r + 1 := by
  classical
  rw [isotropic_intersection_size_bound_chain_image A v hv hr hfix,
    Finset.card_image_of_injOn (isotropic_intersection_size_bound_chain_inj A v hv),
    Finset.card_range]

/-- Quadratic energy of a single chain is at least `(1/2)·chainLen·‖v‖⁴`. -/
lemma isotropic_intersection_size_bound_chain_energy {r : V} (hv : v ≠ 0) (hr : r ∈ A)
    (hfix : isotropic_intersection_size_bound_chainRep A v r = r) :
    (1 / 2) * (isotropic_intersection_size_bound_chainLen A v r : ℝ) * ‖v‖ ^ 4
      ≤ ∑ b ∈ isotropic_intersection_size_bound_chain A v r, (inner (𝕜 := ℝ) b v) ^ 2 := by
  classical
  set n := isotropic_intersection_size_bound_chainLen A v r + 1 with hn
  set s := ‖v‖ ^ 2 with hs
  have hs_pos : 0 < s := by
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [hs]; positivity
  have hncast : ((n : ℝ) - 1) = (isotropic_intersection_size_bound_chainLen A v r : ℝ) := by
    rw [hn]; push_cast; ring
  have h4 : ‖v‖ ^ 4 = s ^ 2 := by
    rw [hs]; ring
  have himg : isotropic_intersection_size_bound_chain A v r
      = (Finset.range n).image (fun i : ℕ => r + (i : ℝ) • v) := by
    rw [isotropic_intersection_size_bound_chain_image A v hv hr hfix, hn]
  have hinj : Set.InjOn (fun i : ℕ => r + (i : ℝ) • v) ↑(Finset.range n) := by
    rw [hn]; exact isotropic_intersection_size_bound_chain_inj A v hv
  have hsum1 : ∑ b ∈ isotropic_intersection_size_bound_chain A v r, (inner (𝕜 := ℝ) b v) ^ 2
      = ∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v + (i : ℝ) * s) ^ 2 := by
    rw [himg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hs]
  have hsplit : ∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v + (i : ℝ) * s) ^ 2
      = s ^ 2 * ∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v / s + (i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h1 : inner (𝕜 := ℝ) r v + (i : ℝ) * s
        = s * (inner (𝕜 := ℝ) r v / s + (i : ℝ)) := by
      field_simp
    rw [h1]; ring
  have hT : (1 / 12) * (n : ℝ) * ((n : ℝ) ^ 2 - 1)
      ≤ ∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v / s + (i : ℝ)) ^ 2 :=
    sum_range_sq_add_ge n (inner (𝕜 := ℝ) r v / s)
  have hcub : (1 / 2) * ((n : ℝ) - 1) ≤ (1 / 12) * (n : ℝ) * ((n : ℝ) ^ 2 - 1) := by
    have := isotropic_chain_cubic_ineq n
    linarith
  have hstep1 : (1 / 2) * (isotropic_intersection_size_bound_chainLen A v r : ℝ) * ‖v‖ ^ 4
      = ((1 / 2) * ((n : ℝ) - 1)) * s ^ 2 := by
    rw [← hncast, h4]
  rw [hstep1, hsum1, hsplit]
  calc ((1 / 2) * ((n : ℝ) - 1)) * s ^ 2
      ≤ ((1 / 12) * (n : ℝ) * ((n : ℝ) ^ 2 - 1)) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hcub (sq_nonneg s)
    _ ≤ (∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v / s + (i : ℝ)) ^ 2) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hT (sq_nonneg s)
    _ = s ^ 2 * ∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v / s + (i : ℝ)) ^ 2 :=
        mul_comm (∑ i ∈ Finset.range n, (inner (𝕜 := ℝ) r v / s + (i : ℝ)) ^ 2) (s ^ 2)

/-- A chain of length `M + 1` contributes exactly `M` points to `v + A`. -/
lemma isotropic_intersection_size_bound_chain_count {r : V} (hv : v ≠ 0) (hr : r ∈ A)
    (hfix : isotropic_intersection_size_bound_chainRep A v r = r) :
    ∑ b ∈ isotropic_intersection_size_bound_chain A v r, (if b - v ∈ A then (1 : ℝ) else 0)
      = (isotropic_intersection_size_bound_chainLen A v r : ℝ) := by
  classical
  have himg : isotropic_intersection_size_bound_chain A v r
      = (Finset.range (isotropic_intersection_size_bound_chainLen A v r + 1)).image
        (fun i : ℕ => r + (i : ℝ) • v) :=
    isotropic_intersection_size_bound_chain_image A v hv hr hfix
  have hinj : Set.InjOn (fun i : ℕ => r + (i : ℝ) • v)
      ↑(Finset.range (isotropic_intersection_size_bound_chainLen A v r + 1)) :=
    isotropic_intersection_size_bound_chain_inj A v hv
  rw [himg, Finset.sum_image hinj, Finset.sum_range_succ']
  have h0 : (if (r + ((0 : ℕ) : ℝ) • v) - v ∈ A then (1 : ℝ) else 0) = 0 := by
    have hnot : r - v ∉ A := by
      rw [← hfix]
      exact isotropic_intersection_size_bound_chainRep_sub_v A v hv hr
    have heq : r + ((0 : ℕ) : ℝ) • v - v = r - v := by simp
    rw [heq]
    simp [hnot]
  rw [h0, add_zero]
  have hk : ∀ k ∈ Finset.range (isotropic_intersection_size_bound_chainLen A v r),
      (if (r + (((k + 1 : ℕ)) : ℝ) • v) - v ∈ A then (1 : ℝ) else 0) = 1 := by
    intro k hk
    have hk' : k < isotropic_intersection_size_bound_chainLen A v r := Finset.mem_range.mp hk
    have heq : r + (((k + 1 : ℕ)) : ℝ) • v - v = r + (k : ℝ) • v := by
      push_cast
      rw [add_smul, one_smul]
      abel
    have hmem : r + (k : ℝ) • v ∈ A := by
      have h1 : r + (k : ℝ) • v
          ∈ (Finset.range (isotropic_intersection_size_bound_chainLen A v r + 1)).image
            (fun i : ℕ => r + (i : ℝ) • v) :=
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      rw [← himg] at h1
      exact ((isotropic_intersection_size_bound_mem_chain A v).mp h1).1
    rw [heq]
    simp [hmem]
  rw [Finset.sum_congr rfl hk]
  simp

end IsotropicIntersectionBoundHelpers

open scoped Pointwise in
/-- Intersection size bound for sets in isotropic position (arXiv:2611.04644 Lemma A.4). -/
theorem isotropic_intersection_size_bound (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (h_nonempty : A.Nonempty)
    (h_mean : ∑ a ∈ A, a = 0)
    (h_cov : ∀ u : EuclideanSpace ℝ (Fin d), ∑ a ∈ A, (inner (𝕜 := ℝ) a u) ^ 2 = (A.card : ℝ) * ‖u‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    ((A ∩ (v +ᵥ A)).card : ℝ) ≤ 2 * (A.card : ℝ) / ‖v‖ ^ 2 := by
  classical
  have hInter : A ∩ (v +ᵥ A) = A.filter (fun a => a - v ∈ A) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_vadd_finset, vadd_eq_add]
    constructor
    · rintro ⟨ha, y, hy, hya⟩
      refine ⟨ha, ?_⟩
      rw [← hya]
      have h : v + y - v = y := by abel
      rw [h]
      exact hy
    · rintro ⟨ha, hav⟩
      exact ⟨ha, a - v, hav, by abel⟩
  have hN : ((A ∩ (v +ᵥ A)).card : ℝ) = ∑ a ∈ A, (if a - v ∈ A then (1 : ℝ) else 0) := by
    rw [hInter]
    exact (Finset.sum_boole (fun a => a - v ∈ A) A).symm
  have hmaps : ∀ a ∈ A, isotropic_intersection_size_bound_chainRep A v a
      ∈ isotropic_intersection_size_bound_chainStarts A v := by
    intro a ha
    exact Finset.mem_image_of_mem _ ha
  have hfib : ∀ r ∈ isotropic_intersection_size_bound_chainStarts A v,
      isotropic_intersection_size_bound_chainRep A v r = r ∧ r ∈ A := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨isotropic_intersection_size_bound_chainRep_fix A v hv ha,
      isotropic_intersection_size_bound_chainRep_mem A v hv ha⟩
  have hcount : ((A ∩ (v +ᵥ A)).card : ℝ)
      = ∑ r ∈ isotropic_intersection_size_bound_chainStarts A v,
          (isotropic_intersection_size_bound_chainLen A v r : ℝ) := by
    rw [hN, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun a : EuclideanSpace ℝ (Fin d) => if a - v ∈ A then (1 : ℝ) else 0)]
    exact Finset.sum_congr rfl (fun r hr =>
      isotropic_intersection_size_bound_chain_count A v hv (hfib r hr).2 (hfib r hr).1)
  have hsplit_energy : ∑ r ∈ isotropic_intersection_size_bound_chainStarts A v,
        ∑ b ∈ isotropic_intersection_size_bound_chain A v r, (inner (𝕜 := ℝ) b v) ^ 2
      = ∑ a ∈ A, (inner (𝕜 := ℝ) a v) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have henergy : ∑ r ∈ isotropic_intersection_size_bound_chainStarts A v,
        (1 / 2) * (isotropic_intersection_size_bound_chainLen A v r : ℝ) * ‖v‖ ^ 4
      ≤ ∑ a ∈ A, (inner (𝕜 := ℝ) a v) ^ 2 := by
    rw [← hsplit_energy]
    exact Finset.sum_le_sum (fun r hr =>
      isotropic_intersection_size_bound_chain_energy A v hv (hfib r hr).2 (hfib r hr).1)
  have hmain : (1 / 2) * ‖v‖ ^ 4 * ((A ∩ (v +ᵥ A)).card : ℝ) ≤ (A.card : ℝ) * ‖v‖ ^ 2 := by
    rw [hcount]
    have hfac : (1 / 2) * ‖v‖ ^ 4 * ∑ r ∈ isotropic_intersection_size_bound_chainStarts A v,
          (isotropic_intersection_size_bound_chainLen A v r : ℝ)
        = ∑ r ∈ isotropic_intersection_size_bound_chainStarts A v,
          (1 / 2) * (isotropic_intersection_size_bound_chainLen A v r : ℝ) * ‖v‖ ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [hfac]
    exact henergy.trans (le_of_eq (h_cov v))
  have hvpos : (0 : ℝ) < ‖v‖ ^ 2 := by
    have h1 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hkey : ‖v‖ ^ 2 * ((A ∩ (v +ᵥ A)).card : ℝ) ≤ 2 * (A.card : ℝ) := by
    have h2 : ‖v‖ ^ 4 * ((A ∩ (v +ᵥ A)).card : ℝ) ≤ 2 * ((A.card : ℝ) * ‖v‖ ^ 2) := by
      nlinarith [hmain]
    have h4 : ‖v‖ ^ 4 = ‖v‖ ^ 2 * ‖v‖ ^ 2 := by ring
    have h3 : ‖v‖ ^ 2 * (‖v‖ ^ 2 * ((A ∩ (v +ᵥ A)).card : ℝ))
        ≤ ‖v‖ ^ 2 * (2 * (A.card : ℝ)) := by
      nlinarith [h2, h4]
    exact le_of_mul_le_mul_left h3 hvpos
  rw [le_div_iff₀ hvpos]
  calc ((A ∩ (v +ᵥ A)).card : ℝ) * ‖v‖ ^ 2
      = ‖v‖ ^ 2 * ((A ∩ (v +ᵥ A)).card : ℝ) := by ring
    _ ≤ 2 * (A.card : ℝ) := hkey
