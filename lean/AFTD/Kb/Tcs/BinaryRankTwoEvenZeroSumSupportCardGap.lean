import AFTD.Prelude
import AFTD.Kb.Tcs.BinarySixZeroSumGramRank

/-!
# binary_rank_two_even_zero_sum_support_card_gap

Topic: quantum   Node: 81e95907e483

Provenance: helper lemma. Supporting OP-3, arXiv:2610.01024, Section E.1; small-support reduction for the three-Hadamard route in IN-184.

A finite set of binary vectors with even cardinality, zero vector sum and Gram rank two has exactly four elements or at least eight.
-/

theorem binary_rank_two_even_zero_sum_support_card_gap {n : ℕ} (S : Finset (Fin n → ZMod 2)) (heven : Even S.card) (hsum : ∑ v ∈ S, v = 0) (hrank : (Matrix.of (fun i j => ∑ v ∈ S, v i * v j)).rank = 2) : S.card = 4 ∨ 8 ≤ S.card := by
  classical
  by_contra hcon
  rw [not_or, not_le] at hcon
  obtain ⟨hne4, hlt8⟩ := hcon
  have hcases : S.card = 0 ∨ S.card = 2 ∨ S.card = 4 ∨ S.card = 6 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hcases with h0 | h2 | h4 | h6
  · have hS : S = ∅ := Finset.card_eq_zero.mp h0
    have hzero : (Matrix.of (fun i j => ∑ v ∈ S, v i * v j)) = 0 := by
      rw [hS]
      ext i j
      simp
    rw [hzero, Matrix.rank_zero] at hrank
    omega
  · obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h2
    rw [hS] at hsum
    rw [Finset.sum_pair hab] at hsum
    have hbb : b + b = (0 : Fin n → ZMod 2) := by
      funext i
      exact CharTwo.add_self_eq_zero (b i)
    have h1 : a + b + b = b := by rw [hsum, zero_add]
    have h2' : a + b + b = a := by rw [add_assoc, hbb, add_zero]
    exact hab (h2'.symm.trans h1)
  · exact hne4 h4
  · let e : ↥S ≃ Fin 6 := (Finset.equivFin S).trans (finCongr h6)
    set v : Fin 6 → (Fin n → ZMod 2) := fun k => (e.symm k).1 with hv
    have hinj : Function.Injective v := by
      intro a b hab
      have h1 : e.symm a = e.symm b := Subtype.ext hab
      exact e.symm.injective h1
    have hSimage : S = Finset.univ.image v := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact ⟨e ⟨x, hx⟩, by simp [hv]⟩
      · rintro ⟨k, rfl⟩
        exact (e.symm k).2
    have hsum6 : ∑ k : Fin 6, v k = 0 := by
      have himg : ∑ k : Fin 6, v k = ∑ x ∈ Finset.univ.image v, x :=
        (Finset.sum_image (s := Finset.univ) (g := v) (f := fun x => x)
          (fun a _ b _ h => hinj h)).symm
      rw [himg, ← hSimage]
      exact hsum
    have hG : (Matrix.of (fun i j => ∑ k : Fin 6, v k i * v k j)) = Matrix.of (fun i j => ∑ x ∈ S, x i * x j) := by
      ext i j
      simp only [Matrix.of_apply]
      have himg : (∑ k : Fin 6, v k i * v k j) = ∑ x ∈ Finset.univ.image v, (x i * x j) :=
        (Finset.sum_image (s := Finset.univ) (g := v) (f := fun x => x i * x j)
          (fun a _ b _ h => hinj h)).symm
      rw [himg, ← hSimage]
    have h4rank := binary_six_zero_sum_gram_rank v hinj hsum6
    rw [hG] at h4rank
    omega
