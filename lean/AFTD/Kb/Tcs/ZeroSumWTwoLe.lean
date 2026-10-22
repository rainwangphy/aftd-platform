import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumW
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq
import AFTD.Kb.Tcs.FinsetFamilyCardSqLeOfInterSymmDiff
import AFTD.Kb.Tcs.ZeroSumEvenSubsetsCardGe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# zero_sum_w_two_le

Topic: combinatorics   Node: 2b3afd6abd09

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems of new types), Theorem 1.2(i) w_r(2) = 2r + 1; the paper's upper bound classifies the w-bad sequences mod 4 (Theorem 3.1); this route replaces the classification by a counting argument.

Upper bound w_r(2) <= 2r + 1: every sequence of 2r + 1 vectors of Z^r, each nonzero mod 2, has a nonempty subsequence whose sum is 0 mod 2 but not 0 mod 4.
-/

/-- For integers, the sum over the symmetric difference plus twice the sum over the
intersection equals the sum of the two sums. -/
lemma zero_sum_w_two_le_sum_symmDiff {ι : Type*} [DecidableEq ι] (f : ι → ℤ)
    (I J : Finset ι) :
    ∑ i ∈ symmDiff I J, f i + 2 * ∑ i ∈ I ∩ J, f i = ∑ i ∈ I, f i + ∑ i ∈ J, f i := by
  have h1 := Finset.sum_inter_add_sum_sdiff I J f
  have h2 := Finset.sum_inter_add_sum_sdiff J I f
  rw [Finset.inter_comm J I] at h2
  have hdisj : Disjoint (I \ J) (J \ I) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx.2 hx'.1
  have h3 : ∑ i ∈ I \ J, f i + ∑ i ∈ J \ I, f i = ∑ i ∈ symmDiff I J, f i := by
    rw [Finset.symmDiff_def, Finset.sum_union hdisj]
  omega

theorem zero_sum_w_two_le (r : ℕ) : zero_sum_w r 2 ≤ ((2 * r + 1 : ℕ) : ℕ∞) := by
  refine iInf₂_le (f := fun (N : ℕ) (_ : ∀ A : List (Fin r → ℤ), A.length = N →
    zero_sum_admissible 2 A → ∃ I, zero_sum_good_subseq 2 A I) => (N : ℕ∞)) (2 * r + 1) ?_
  intro A hlen hadm
  by_contra hcon
  push Not at hcon
  set a : Fin A.length → Fin r → ℤ := fun i j => A.get i j with ha
  set K : Finset (Finset (Fin A.length)) :=
    (Finset.univ : Finset (Finset (Fin A.length))).filter (fun I => ∀ j, (2 : ℤ) ∣ ∑ i ∈ I, a i j)
    with hK
  have hKmem : ∀ I : Finset (Fin A.length), I ∈ K ↔ ∀ j, (2 : ℤ) ∣ ∑ i ∈ I, a i j := by
    intro I
    rw [hK]
    simp
  have hbad : ∀ I ∈ K, ∀ j, (4 : ℤ) ∣ ∑ i ∈ I, a i j := by
    intro I hI j
    have hev := (hKmem I).1 hI
    rcases Finset.eq_empty_or_nonempty I with h | hne
    · subst h
      simp
    · by_contra h4
      refine hcon I ?_
      rw [zero_sum_good_subseq]
      refine ⟨hne, fun j => hev j, j, ?_⟩
      norm_num
      exact h4
  have hKsd : ∀ I ∈ K, ∀ J ∈ K, symmDiff I J ∈ K := by
    intro I hI J hJ
    rw [hKmem]
    intro j
    have e1 : (2 : ℤ) ∣ ∑ i ∈ I, a i j := (hKmem I).1 hI j
    have e2 : (2 : ℤ) ∣ ∑ i ∈ J, a i j := (hKmem J).1 hJ j
    have hid := zero_sum_w_two_le_sum_symmDiff (f := fun i => a i j) I J
    have hEq : ∑ i ∈ symmDiff I J, a i j
        = ∑ i ∈ I, a i j + ∑ i ∈ J, a i j - 2 * ∑ i ∈ I ∩ J, a i j := by linarith
    rw [hEq]
    exact dvd_sub (dvd_add e1 e2) (dvd_mul_right 2 _)
  have hKinter : ∀ I ∈ K, ∀ J ∈ K, I ∩ J ∈ K := by
    intro I hI J hJ
    rw [hKmem]
    intro j
    have hid := zero_sum_w_two_le_sum_symmDiff (f := fun i => a i j) I J
    have eI := hbad I hI j
    have eJ := hbad J hJ j
    have eS := hbad (symmDiff I J) (hKsd I hI J hJ) j
    have hEq : 2 * ∑ i ∈ I ∩ J, a i j
        = ∑ i ∈ I, a i j + ∑ i ∈ J, a i j - ∑ i ∈ symmDiff I J, a i j := by linarith
    have h4 : (4 : ℤ) ∣ 2 * ∑ i ∈ I ∩ J, a i j := by
      rw [hEq]
      exact dvd_sub (dvd_add eI eJ) eS
    obtain ⟨k, hk⟩ := h4
    exact ⟨k, by linarith⟩
  have h1 : K.card ^ 2 ≤ 2 ^ (Finset.univ : Finset (Fin A.length)).card := by
    refine finset_family_card_sq_le_of_inter_symm_diff (Finset.univ : Finset (Fin A.length)) K
      (fun I _ => Finset.subset_univ I) ?_ hKinter hKsd ?_
    · rw [hKmem]; intro j; simp
    · intro x hx
      rw [hKmem] at hx
      obtain ⟨j, hj⟩ := hadm (A.get x) (List.get_mem A x)
      exact hj (by simpa [ha] using hx j)
  have h2 : 2 ^ (Finset.univ : Finset (Fin A.length)).card ≤ 2 ^ r * K.card := by
    have h := zero_sum_even_subsets_card_ge (ι := Fin A.length) r a
    simpa [hK] using h
  have hcard_pos : 0 < K.card := by
    rw [Finset.card_pos]
    refine ⟨∅, ?_⟩
    rw [hKmem]
    intro j
    simp
  have hKle : K.card ≤ 2 ^ r := by
    have h3 : K.card ^ 2 ≤ 2 ^ r * K.card := le_trans h1 h2
    rw [pow_two] at h3
    exact Nat.le_of_mul_le_mul_right h3 hcard_pos
  have h4 : 2 ^ (2 * r + 1) ≤ 2 ^ r * 2 ^ r := by
    have h3 : 2 ^ (Finset.univ : Finset (Fin A.length)).card ≤ 2 ^ r * K.card := h2
    have h5 : 2 ^ r * K.card ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_left _ hKle
    have h6 : (Finset.univ : Finset (Fin A.length)).card = 2 * r + 1 := by
      simp [Fintype.card_fin, hlen]
    rw [h6] at h3
    exact le_trans h3 h5
  have h5 : 2 ^ r * 2 ^ r = 2 ^ (2 * r) := by
    rw [← pow_add]
    ring_nf
  rw [h5] at h4
  have h6 : 2 ^ (2 * r + 1) = 2 * 2 ^ (2 * r) := by
    rw [pow_succ]
    ring
  rw [h6] at h4
  have hpos : 0 < 2 ^ (2 * r) := pow_pos (by norm_num) _
  omega
