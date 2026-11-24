import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq
import AFTD.Kb.Tcs.ZeroSumWBad

/-!
# zero_sum_w_bad_replicate_le

Topic: combinatorics   Node: 8ab2800c6f11

Provenance: helper lemma. step towards zero_sum_w_eq_question

A constant sequence of length k is w-bad only if k ≤ n - 1.
-/

/-- A constant sequence of length k is w-bad only if k ≤ n - 1. -/
theorem zero_sum_w_bad_replicate_le (n r k : ℕ) (hn : 1 < n) (x : Fin r → ℤ) (hk : 1 ≤ k) (hbad : zero_sum_w_bad n (List.replicate k x)) : k ≤ n - 1 := by
  by_contra! hgt
  have hlen : (List.replicate k x).length = k := List.length_replicate
  let I : Finset (Fin (List.replicate k x).length) :=
    Finset.image (fun (i : Fin n) => ⟨i.val, by rw [hlen]; omega⟩) Finset.univ
  have hIne : I.Nonempty := by
    use ⟨0, by rw [hlen]; omega⟩
    apply Finset.mem_image.mpr
    use ⟨0, by omega⟩
    exact ⟨Finset.mem_univ _, rfl⟩
  have h_elem : ∀ i ∈ I, (List.replicate k x).get i = x := by
    intro i hi
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
    have : (List.replicate k x).get i = (List.replicate k x)[i.val] := rfl
    rw [this, List.getElem_replicate]
  have h_card : I.card = n := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin n
    · intro a b hab
      ext
      injection hab
  have h_sum : ∀ j, ∑ i ∈ I, (List.replicate k x).get i j = (n : ℤ) * x j := by
    intro j
    have : ∑ i ∈ I, (List.replicate k x).get i j = ∑ i ∈ I, x j := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [h_elem i hi]
    rw [this, Finset.sum_const, h_card, nsmul_eq_mul]
  have h_good : zero_sum_good_subseq n (List.replicate k x) I := by
    refine ⟨hIne, fun j => ?_, ?_⟩
    · rw [h_sum j]
      exact dvd_mul_right (n : ℤ) (x j)
    · obtain ⟨j, hj⟩ := hbad.1 x (List.mem_replicate.mpr ⟨by omega, rfl⟩)
      use j
      rw [h_sum j]
      intro hdiv
      apply hj
      have hn_ne : (n : ℤ) ≠ 0 := by omega
      have hsq : (n : ℤ) ^ 2 = (n : ℤ) * (n : ℤ) := sq (n : ℤ)
      rw [hsq] at hdiv
      exact (mul_dvd_mul_iff_left hn_ne).mp hdiv
  exact hbad.2 I h_good
