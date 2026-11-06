import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetDotProductSet
import AFTD.Kb.Tcs.SumsetRepCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SumsetSumVectorsFinset
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# sumset_rep_support_and_symmetry

Topic: combinatorics   Node: cffdb979605c

Provenance: formalization of a published result. Source: arXiv:2611.07303 Proposition 5.7

Let k ≥ 3, h ≥ 2, and q ≥ k be integers. Then sumset_dot_product_set h k q = Finset.Icc ((h : ℤ) + 1) (((h : ℤ) + 1) * (q : ℤ)), its cardinality is (h + 1) * q - h, and for every integer s, sumset_rep_count h k q s = sumset_rep_count h k q (((h : ℤ) + 1) * ((q : ℤ) + 1) - s).
-/

private theorem sumset_rep_support_and_symmetry_aux_sum_orderEmb {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (f : α → ℤ) :
    ∑ i : Fin k, f (s.orderEmbOfFin h i) = ∑ a ∈ s, f a := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
  rw [Finset.sum_map]; rfl

private theorem sumset_rep_support_and_symmetry_aux_mem_vectors (h k : ℕ) (x : Fin k → ℤ) :
    x ∈ sumset_sum_vectors_finset h k ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ (h : ℤ)) ∧ ∑ i, x i = (h : ℤ) := by
  unfold sumset_sum_vectors_finset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h1 i
    simp only [Finset.mem_image, Finset.mem_range] at this
    obtain ⟨n, hn, heq⟩ := this
    rw [← heq]; constructor <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨h0, hle⟩ := h1 i
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨(x i).toNat, by omega, by omega⟩

private theorem sumset_rep_support_and_symmetry_aux_sorted (k : ℕ) (A : Finset ℤ)
    (hA : A.card = k) : sumset_finset_sorted_vector k A = A.orderEmbOfFin hA := by
  unfold sumset_finset_sorted_vector
  rw [dif_pos hA]

private theorem sumset_rep_support_and_symmetry_aux_sum_rev (k : ℕ) (f : Fin k → ℤ) :
    ∑ i : Fin k, f i.rev = ∑ i : Fin k, f i := by
  have := Equiv.sum_comp
    (⟨Fin.rev, Fin.rev, fun i => Fin.rev_rev i, fun i => Fin.rev_rev i⟩ : Fin k ≃ Fin k) f
  simpa using this

private theorem sumset_rep_support_and_symmetry_aux_reflect_inj (q : ℕ) :
    Function.Injective (fun a : ℤ => (q : ℤ) + 1 - a) := by
  intro a b hab
  have := congrArg (fun t : ℤ => (q : ℤ) + 1 - t) hab
  simpa using this

private theorem sumset_rep_support_and_symmetry_aux_reflect_invol (q : ℕ) (A : Finset ℤ) :
    (A.image (fun a => (q : ℤ) + 1 - a)).image (fun a => (q : ℤ) + 1 - a) = A := by
  rw [Finset.image_image]
  have hc : ((fun a : ℤ => (q : ℤ) + 1 - a) ∘ fun a => (q : ℤ) + 1 - a) = id := by
    funext a; simp
  rw [hc, Finset.image_id]

private theorem sumset_rep_support_and_symmetry_aux_orderEmb_image (k q : ℕ) (A : Finset ℤ)
    (hA : A.card = k) (hB : (A.image (fun a => (q : ℤ) + 1 - a)).card = k) (i : Fin k) :
    (A.image (fun a => (q : ℤ) + 1 - a)).orderEmbOfFin hB i
      = (q : ℤ) + 1 - A.orderEmbOfFin hA i.rev := by
  have hmono : StrictMono (fun i : Fin k => (q : ℤ) + 1 - A.orderEmbOfFin hA i.rev) := by
    intro i j hij
    have h1 : j.rev < i.rev := by rw [Fin.rev_lt_iff]; simpa using hij
    have h2 := (A.orderEmbOfFin hA).strictMono h1
    show (q : ℤ) + 1 - A.orderEmbOfFin hA i.rev < (q : ℤ) + 1 - A.orderEmbOfFin hA j.rev
    omega
  have hmem : ∀ i : Fin k,
      (q : ℤ) + 1 - A.orderEmbOfFin hA i.rev ∈ A.image (fun a => (q : ℤ) + 1 - a) :=
    fun i => Finset.mem_image.mpr ⟨_, Finset.orderEmbOfFin_mem A hA i.rev, rfl⟩
  have heq := Finset.orderEmbOfFin_unique hB hmem hmono
  exact (congrFun heq i).symm

private theorem sumset_rep_support_and_symmetry_aux_dot_reflect (k q : ℕ) (x : Fin k → ℤ)
    (A : Finset ℤ) (hA : A.card = k)
    (hB : (A.image (fun a => (q : ℤ) + 1 - a)).card = k) :
    (fun i => x i.rev) ⬝ᵥ sumset_finset_sorted_vector k (A.image (fun a => (q : ℤ) + 1 - a))
      = ((q : ℤ) + 1) * (∑ i, x i) - x ⬝ᵥ sumset_finset_sorted_vector k A := by
  rw [sumset_rep_support_and_symmetry_aux_sorted k _ hB,
    sumset_rep_support_and_symmetry_aux_sorted k A hA, dotProduct, dotProduct]
  have himg : ∀ i : Fin k, (A.image (fun a => (q : ℤ) + 1 - a)).orderEmbOfFin hB i
      = (q : ℤ) + 1 - A.orderEmbOfFin hA i.rev :=
    sumset_rep_support_and_symmetry_aux_orderEmb_image k q A hA hB
  simp only [himg]
  have hstep : ∀ i : Fin k, x i.rev * ((q : ℤ) + 1 - A.orderEmbOfFin hA i.rev)
      = ((q : ℤ) + 1) * x i.rev - x i.rev * A.orderEmbOfFin hA i.rev := fun i => by ring
  simp only [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sumset_rep_support_and_symmetry_aux_sum_rev k x,
    sumset_rep_support_and_symmetry_aux_sum_rev k (fun i => x i * A.orderEmbOfFin hA i)]

private theorem sumset_rep_support_and_symmetry_aux_reflect_card (k q : ℕ) (A : Finset ℤ)
    (hA : A.card = k) : (A.image (fun a => (q : ℤ) + 1 - a)).card = k := by
  rw [Finset.card_image_of_injective _ (sumset_rep_support_and_symmetry_aux_reflect_inj q), hA]

private theorem sumset_rep_support_and_symmetry_aux_reflect_subset (q : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (q : ℤ)) :
    A.image (fun a => (q : ℤ) + 1 - a) ⊆ Finset.Icc (1 : ℤ) (q : ℤ) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have ha' := hA ha
  rw [Finset.mem_Icc] at ha' ⊢
  omega

private theorem sumset_rep_support_and_symmetry_aux_phi_mem (h k q : ℕ) (x : Fin k → ℤ)
    (A : Finset ℤ) (hx : x ∈ sumset_sum_vectors_finset (h + 1) k)
    (hA : A ∈ Finset.powersetCard k (Finset.Icc (1 : ℤ) (q : ℤ))) :
    ((fun i => x i.rev), A.image (fun a => (q : ℤ) + 1 - a)) ∈
      sumset_sum_vectors_finset (h + 1) k ×ˢ
        Finset.powersetCard k (Finset.Icc (1 : ℤ) (q : ℤ)) := by
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · rw [sumset_rep_support_and_symmetry_aux_mem_vectors] at hx ⊢
    refine ⟨fun i => hx.1 i.rev, ?_⟩
    rw [sumset_rep_support_and_symmetry_aux_sum_rev]; exact hx.2
  · rw [Finset.mem_powersetCard] at hA ⊢
    exact ⟨sumset_rep_support_and_symmetry_aux_reflect_subset q A hA.1,
      sumset_rep_support_and_symmetry_aux_reflect_card k q A hA.2⟩

private theorem sumset_rep_support_and_symmetry_aux_dot_phi (h k q : ℕ) (x : Fin k → ℤ)
    (A : Finset ℤ) (hx : x ∈ sumset_sum_vectors_finset (h + 1) k)
    (hA : A ∈ Finset.powersetCard k (Finset.Icc (1 : ℤ) (q : ℤ))) :
    (fun i => x i.rev) ⬝ᵥ sumset_finset_sorted_vector k (A.image (fun a => (q : ℤ) + 1 - a))
      = ((h : ℤ) + 1) * ((q : ℤ) + 1) - x ⬝ᵥ sumset_finset_sorted_vector k A := by
  rw [Finset.mem_powersetCard] at hA
  obtain ⟨hAsub, hAcard⟩ := hA
  rw [sumset_rep_support_and_symmetry_aux_dot_reflect k q x A hAcard
    (sumset_rep_support_and_symmetry_aux_reflect_card k q A hAcard)]
  have hsum : ∑ i, x i = ((h : ℤ) + 1) := by
    have h2 : ((h + 1 : ℕ) : ℤ) = (h : ℤ) + 1 := by push_cast; ring
    have := (sumset_rep_support_and_symmetry_aux_mem_vectors (h + 1) k x).mp hx
    rw [h2] at this
    exact this.2
  rw [hsum]; ring

private theorem sumset_rep_support_and_symmetry_aux_hfun (h k q : ℕ) (s : ℤ) :
    sumset_rep_count h k q s =
      ((sumset_sum_vectors_finset (h+1) k ×ˢ
        Finset.powersetCard k (Finset.Icc (1 : ℤ) (q : ℤ))).filter
        (fun p : (Fin k → ℤ) × Finset ℤ => p.1 ⬝ᵥ sumset_finset_sorted_vector k p.2 = s)).card := by
  rw [sumset_rep_count]

private theorem sumset_rep_support_and_symmetry_aux_card_arith (h q : ℕ) (hq : 1 ≤ q) :
    (((h : ℤ) + 1) * (q : ℤ) + 1 - ((h : ℤ) + 1)).toNat = (h + 1) * q - h := by
  have hle : h ≤ (h + 1) * q := by nlinarith
  have h1 : ((h : ℤ) + 1) * (q : ℤ) + 1 - ((h : ℤ) + 1) = (((h + 1) * q - h : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [h1, Int.toNat_natCast]

private theorem sumset_rep_support_and_symmetry_aux_exists (S T : Finset ℤ) (k : ℕ)
    (hT : T ⊆ S) (hkT : T.card ≤ k) (hcard : k ≤ S.card) :
    ∃ A, T ⊆ A ∧ A ⊆ S ∧ A.card = k := by
  have hle : k - T.card ≤ (S \ T).card := by
    rw [Finset.card_sdiff_of_subset hT]; omega
  obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq hle
  refine ⟨T ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hT h
    · exact (Finset.mem_sdiff.mp (hUS h)).1
  · rw [Finset.card_union_of_disjoint]
    · omega
    · rw [Finset.disjoint_left]
      intro x hxT hxU
      exact (Finset.mem_sdiff.mp (hUS hxU)).2 hxT

private theorem sumset_rep_support_and_symmetry_aux_sum_ite (A : Finset ℤ) (d : ℤ) (hd : d ∈ A)
    (c : ℤ) : ∑ z ∈ A, (if z = d then c else 0) = c := by
  rw [Finset.sum_ite_eq']; simp [hd]

private theorem sumset_rep_support_and_symmetry_aux_sum_ite_mul (A : Finset ℤ) (d : ℤ)
    (hd : d ∈ A) (c : ℤ) : ∑ z ∈ A, (if z = d then c else 0) * z = c * d := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']; simp [hd]

private theorem sumset_rep_support_and_symmetry_aux_achiev_aux (A : Finset ℤ) (k h : ℕ)
    (hA : A.card = k) (m : ℤ → ℤ) (hm0 : ∀ z, 0 ≤ m z) (hmh : ∀ z, m z ≤ (h : ℤ) + 1)
    (hmsum : ∑ z ∈ A, m z = (h : ℤ) + 1) :
    (fun i => m (A.orderEmbOfFin hA i)) ∈ sumset_sum_vectors_finset (h+1) k ∧
    (fun i => m (A.orderEmbOfFin hA i)) ⬝ᵥ sumset_finset_sorted_vector k A
      = ∑ z ∈ A, m z * z := by
  have hsorted : sumset_finset_sorted_vector k A = A.orderEmbOfFin hA :=
    sumset_rep_support_and_symmetry_aux_sorted k A hA
  constructor
  · rw [sumset_rep_support_and_symmetry_aux_mem_vectors]
    refine ⟨fun i => ?_, ?_⟩
    · exact ⟨hm0 _, hmh _⟩
    · rw [sumset_rep_support_and_symmetry_aux_sum_orderEmb]; exact hmsum
  · rw [hsorted, dotProduct]
    exact sumset_rep_support_and_symmetry_aux_sum_orderEmb A hA (fun z => m z * z)

private theorem sumset_rep_support_and_symmetry_aux_mem_of (h k q : ℕ) (hk : 3 ≤ k)
    (hq : k ≤ q) (n : ℤ) (hn1 : (h : ℤ) + 1 ≤ n)
    (hn2 : n ≤ ((h : ℤ) + 1) * (q : ℤ)) :
    n ∈ sumset_dot_product_set h k q := by
  set H : ℤ := (h : ℤ) + 1 with hH
  have hHpos : 0 < H := by omega
  have hHne : H ≠ 0 := ne_of_gt hHpos
  obtain ⟨d, r, hnr, hr0, hrlt⟩ : ∃ d r : ℤ, n = d * H + r ∧ 0 ≤ r ∧ r < H := by
    refine ⟨n / H, n % H, ?_, Int.emod_nonneg n hHne, Int.emod_lt_of_pos n hHpos⟩
    exact (Int.ediv_mul_add_emod n H).symm
  have hd1 : 1 ≤ d := by nlinarith [hrlt, hn1]
  have hdq : d ≤ (q : ℤ) := by nlinarith [hr0, hn2]
  set S : Finset ℤ := Finset.Icc (1 : ℤ) (q : ℤ) with hSdef
  have hScard : S.card = q := by
    rw [hSdef, Int.card_Icc]; simp
  have hdmem : d ∈ S := by rw [hSdef, Finset.mem_Icc]; exact ⟨hd1, hdq⟩
  by_cases hr : r = 0
  · have hsub : ({d} : Finset ℤ) ⊆ S := by
      intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hdmem
    have hcard1 : ({d} : Finset ℤ).card ≤ k := by simp; omega
    obtain ⟨A, hTA, hAS, hAcard⟩ :=
      sumset_rep_support_and_symmetry_aux_exists S {d} k hsub hcard1 (by rw [hScard]; exact hq)
    have hdA : d ∈ A := hTA (Finset.mem_singleton_self d)
    set m : ℤ → ℤ := fun z => if z = d then H else 0 with hmdef
    have hm0 : ∀ z, 0 ≤ m z := by
      intro z; simp only [hmdef]; split_ifs <;> omega
    have hmh : ∀ z, m z ≤ (h : ℤ) + 1 := by
      intro z; simp only [hmdef]; split_ifs <;> omega
    have hmsum : ∑ z ∈ A, m z = (h : ℤ) + 1 := by
      have h1 : ∑ z ∈ A, m z = H := by
        simp only [hmdef]; exact sumset_rep_support_and_symmetry_aux_sum_ite A d hdA H
      rw [h1, hH]
    have hmdot : ∑ z ∈ A, m z * z = n := by
      have h1 : ∑ z ∈ A, m z * z = H * d := by
        simp only [hmdef]; exact sumset_rep_support_and_symmetry_aux_sum_ite_mul A d hdA H
      rw [h1, hnr, hr]; ring
    obtain ⟨hxS, hxdot⟩ := sumset_rep_support_and_symmetry_aux_achiev_aux A k h hAcard m hm0 hmh hmsum
    refine Finset.mem_image.mpr ⟨((fun i => m (A.orderEmbOfFin hAcard i)), A), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hxS, Finset.mem_powersetCard.mpr ⟨hAS, hAcard⟩⟩
    · exact hxdot.trans hmdot
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hdltq : d < (q : ℤ) := by nlinarith [hrpos, hn2]
    have hd1mem : d + 1 ∈ S := by rw [hSdef, Finset.mem_Icc]; constructor <;> omega
    have hsub : ({d, d+1} : Finset ℤ) ⊆ S := by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hdmem
      · exact hd1mem
    have hcard2 : ({d, d+1} : Finset ℤ).card ≤ k := by
      rw [Finset.card_pair_eq_two_iff.mpr (by omega : d ≠ d + 1)]; omega
    obtain ⟨A, hTA, hAS, hAcard⟩ :=
      sumset_rep_support_and_symmetry_aux_exists S {d, d+1} k hsub hcard2
        (by rw [hScard]; exact hq)
    have hdA : d ∈ A := hTA (by simp)
    have hd1A : d + 1 ∈ A := hTA (by simp)
    set m : ℤ → ℤ := fun z => (if z = d then (H - r) else 0) + (if z = d+1 then r else 0)
      with hmdef
    have hsum_eq : ∑ z ∈ A, m z = (H - r) + r := by
      simp only [hmdef, Finset.sum_add_distrib]
      rw [sumset_rep_support_and_symmetry_aux_sum_ite A d hdA (H - r),
        sumset_rep_support_and_symmetry_aux_sum_ite A (d+1) hd1A r]
    have hmsum : ∑ z ∈ A, m z = (h : ℤ) + 1 := by
      rw [hsum_eq, hH]; ring
    have hmdot : ∑ z ∈ A, m z * z = n := by
      have h1 : ∑ z ∈ A, m z * z = (H - r) * d + r * (d + 1) := by
        simp only [hmdef, add_mul, Finset.sum_add_distrib]
        rw [sumset_rep_support_and_symmetry_aux_sum_ite_mul A d hdA (H - r),
          sumset_rep_support_and_symmetry_aux_sum_ite_mul A (d+1) hd1A r]
      rw [h1, hnr]; ring
    have hm0 : ∀ z, 0 ≤ m z := by
      intro z; simp only [hmdef]; split_ifs <;> omega
    have hmh : ∀ z, m z ≤ (h : ℤ) + 1 := by
      intro z; simp only [hmdef]; split_ifs <;> omega
    obtain ⟨hxS, hxdot⟩ := sumset_rep_support_and_symmetry_aux_achiev_aux A k h hAcard m hm0 hmh hmsum
    refine Finset.mem_image.mpr ⟨((fun i => m (A.orderEmbOfFin hAcard i)), A), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hxS, Finset.mem_powersetCard.mpr ⟨hAS, hAcard⟩⟩
    · exact hxdot.trans hmdot

private theorem sumset_rep_support_and_symmetry_aux_subset (h k q : ℕ) (n : ℤ)
    (hn : n ∈ sumset_dot_product_set h k q) :
    (h : ℤ) + 1 ≤ n ∧ n ≤ ((h : ℤ) + 1) * (q : ℤ) := by
  unfold sumset_dot_product_set at hn
  rw [Finset.mem_image] at hn
  obtain ⟨p, hp, hpn⟩ := hn
  obtain ⟨x, A⟩ := p
  simp only at hpn
  rw [Finset.mem_product] at hp
  simp only at hp
  obtain ⟨hxb, hAb⟩ := hp
  rw [sumset_rep_support_and_symmetry_aux_mem_vectors] at hxb
  obtain ⟨hx0, hxsum⟩ := hxb
  rw [Finset.mem_powersetCard] at hAb
  obtain ⟨hAS, hAcard⟩ := hAb
  have hbound : ∀ i : Fin k,
      (1 : ℤ) ≤ A.orderEmbOfFin hAcard i ∧ A.orderEmbOfFin hAcard i ≤ (q : ℤ) := by
    intro i
    have hh := hAS (Finset.orderEmbOfFin_mem A hAcard i)
    rw [Finset.mem_Icc] at hh
    exact hh
  have hdot : x ⬝ᵥ sumset_finset_sorted_vector k A
      = ∑ i : Fin k, x i * A.orderEmbOfFin hAcard i := by
    rw [sumset_rep_support_and_symmetry_aux_sorted k A hAcard]
    simp only [dotProduct]
  have hn' : n = ∑ i : Fin k, x i * A.orderEmbOfFin hAcard i := by rw [← hpn, hdot]
  constructor
  · rw [hn']
    have h1 : ∑ i : Fin k, x i = (h : ℤ) + 1 := by
      rw [hxsum]; push_cast; ring
    rw [← h1]
    apply Finset.sum_le_sum
    intro i _
    calc x i = x i * 1 := by ring
      _ ≤ x i * A.orderEmbOfFin hAcard i :=
        mul_le_mul_of_nonneg_left (hbound i).1 (hx0 i).1
  · rw [hn']
    have h1 : ∑ i : Fin k, x i * A.orderEmbOfFin hAcard i ≤ ∑ i : Fin k, x i * (q : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hbound i).2 (hx0 i).1
    have h2 : ∑ i : Fin k, x i * (q : ℤ) = (((h+1 : ℕ)) : ℤ) * (q : ℤ) := by
      rw [← Finset.sum_mul, hxsum]
    rw [h2] at h1
    have h3 : (((h+1 : ℕ)) : ℤ) = (h : ℤ) + 1 := by push_cast; ring
    rw [h3] at h1
    exact h1

/-- Proposition 5.7: Support and Reflection Symmetry of Sumset Representation Counts. -/
theorem sumset_rep_support_and_symmetry (k h q : ℕ)
    (hk : 3 ≤ k) (hh : 2 ≤ h) (hq : k ≤ q) :
    sumset_dot_product_set h k q = Finset.Icc ((h : ℤ) + 1) (((h : ℤ) + 1) * (q : ℤ)) ∧
    (sumset_dot_product_set h k q).card = (h + 1) * q - h ∧
    ∀ s : ℤ, sumset_rep_count h k q s =
      sumset_rep_count h k q (((h : ℤ) + 1) * ((q : ℤ) + 1) - s) := by
  have hiff : ∀ n : ℤ,
      (n ∈ sumset_dot_product_set h k q ↔ (h : ℤ) + 1 ≤ n ∧ n ≤ ((h : ℤ) + 1) * (q : ℤ)) :=
    fun n => ⟨sumset_rep_support_and_symmetry_aux_subset h k q n,
      fun hn => sumset_rep_support_and_symmetry_aux_mem_of h k q hk hq n hn.1 hn.2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext n
    rw [Finset.mem_Icc]
    exact hiff n
  · have hset : sumset_dot_product_set h k q
        = Finset.Icc ((h : ℤ) + 1) (((h : ℤ) + 1) * (q : ℤ)) := by
      ext n; rw [Finset.mem_Icc]; exact hiff n
    rw [hset, Int.card_Icc, sumset_rep_support_and_symmetry_aux_card_arith h q (by omega)]
  · intro s
    set C : ℤ := ((h : ℤ) + 1) * ((q : ℤ) + 1) with hC
    have key : ∀ t : ℤ, sumset_rep_count h k q t =
        ((sumset_sum_vectors_finset (h+1) k ×ˢ
          Finset.powersetCard k (Finset.Icc (1 : ℤ) (q : ℤ))).filter
          (fun p : (Fin k → ℤ) × Finset ℤ =>
            p.1 ⬝ᵥ sumset_finset_sorted_vector k p.2 = t)).card :=
      fun t => sumset_rep_support_and_symmetry_aux_hfun h k q t
    rw [key s, key (C - s)]
    refine Finset.card_bij
      (fun (p : (Fin k → ℤ) × Finset ℤ) (_ : p ∈ _) =>
        ((fun i : Fin k => p.1 (Fin.rev i)), p.2.image (fun a => (q : ℤ) + 1 - a)))
      ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hp1, hp2⟩ := hp
      rw [Finset.mem_product] at hp1
      refine ⟨?_, ?_⟩
      · exact sumset_rep_support_and_symmetry_aux_phi_mem h k q p.1 p.2 hp1.1 hp1.2
      · rw [sumset_rep_support_and_symmetry_aux_dot_phi h k q p.1 p.2 hp1.1 hp1.2, hp2]
    · intro p1 h1 p2 h2 heq
      have h1' : p1.1 = p2.1 := by
        have := congrArg (fun t : Fin k → ℤ => fun i : Fin k => t (Fin.rev i))
          (congrArg Prod.fst heq)
        simpa using this
      have h2' : p1.2 = p2.2 := by
        have := congrArg (fun t : Finset ℤ => t.image (fun a => (q : ℤ) + 1 - a))
          (congrArg Prod.snd heq)
        simpa only [sumset_rep_support_and_symmetry_aux_reflect_invol] using this
      exact Prod.ext h1' h2'
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [Finset.mem_product] at hb1
      refine ⟨((fun i : Fin k => b.1 (Fin.rev i)), b.2.image (fun a => (q : ℤ) + 1 - a)),
        ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨sumset_rep_support_and_symmetry_aux_phi_mem h k q b.1 b.2 hb1.1 hb1.2, ?_⟩
        rw [sumset_rep_support_and_symmetry_aux_dot_phi h k q b.1 b.2 hb1.1 hb1.2, hb2]
        ring
      · have hf : (fun i : Fin k => (fun j : Fin k => b.1 (Fin.rev j)) (Fin.rev i)) = b.1 := by
          funext i
          simp
        show (((fun i : Fin k => (fun j : Fin k => b.1 (Fin.rev j)) (Fin.rev i))),
            (b.2.image (fun a => (q : ℤ) + 1 - a)).image (fun a => (q : ℤ) + 1 - a))
            = (b.1, b.2)
        rw [hf, sumset_rep_support_and_symmetry_aux_reflect_invol]
