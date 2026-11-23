import AFTD.Prelude
import AFTD.Kb.Tcs.IsJointPerfectCode
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.CardHammingRing
import AFTD.Kb.Tcs.CardHammingBall

/-!
# joint_perfect_code_partition

Topic: information   Node: 79ad5a51ddb5

Provenance: helper lemma. arXiv:2611.18156, Lemma IV.1

If C ⊆ Fin n → Fin q is a (c, c') joint perfect code, then for any fixed codeword x₀ ∈ C, every word y : Fin n → Fin q either belongs to the radius-c Hamming ball around some codeword x ∈ C or belongs to the (c, c') Hamming ring centered at x₀.
-/

/-- A (c, c') joint perfect code partitions the space into radius-c balls around each codeword and the (c, c') ring around any fixed codeword. -/
lemma joint_perfect_code_partition {n q c c' : ℕ}
    (C : Finset (Fin n → Fin q)) (hC : is_joint_perfect_code c c' C)
    {x₀ : Fin n → Fin q} (hx₀ : x₀ ∈ C) (y : Fin n → Fin q) :
    (∃ x ∈ C, y ∈ hamming_ball c x) ∨ y ∈ hamming_ring c c' x₀ := by
  classical
  obtain ⟨hECD, hcount⟩ := hC
  obtain ⟨hdisj, hdisj_ring⟩ := hECD
  by_cases hcn : n ≤ c
  · refine Or.inl ⟨x₀, hx₀, ?_⟩
    simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_trans (by simpa using hammingDist_le_card_fintype (x := x₀) (y := y)) hcn
  by_cases hq1 : q ≤ 1
  · have hsub : Subsingleton (Fin q) := by
      rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_fin]
      exact hq1
    haveI := hsub
    refine Or.inl ⟨x₀, hx₀, ?_⟩
    simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hammingDist_eq_zero.mpr (Subsingleton.elim x₀ y)]
    exact Nat.zero_le c
  have hcn' : c < n := not_le.mp hcn
  have hq2 : 2 ≤ q := by have := not_le.mp hq1; omega
  have hc_le : c ≤ n := le_of_lt hcn'
  by_cases hcc' : c + c' ≤ n
  · have hball_c : ∀ x : Fin n → Fin q,
        (hamming_ball c x).card = ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i :=
      fun x => card_hamming_ball n q c hq2 hc_le x
    have hring : (hamming_ring c c' x₀).card =
        ∑ j ∈ Finset.Icc (c + 1) (c + c'), n.choose j * (q - 1) ^ j :=
      card_hamming_ring n q c c' hq2 hcc' x₀
    have hcardA : (C.biUnion (fun x => hamming_ball c x)).card =
        C.card * ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i := by
      rw [Finset.card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun x _ => hball_c x), Finset.sum_const, Nat.nsmul_eq_mul]
    have hdisjAB : Disjoint (C.biUnion (fun x => hamming_ball c x)) (hamming_ring c c' x₀) := by
      rw [Finset.disjoint_biUnion_left]
      exact fun x hx => hdisj_ring x hx x₀ hx₀
    have hUcard : (C.biUnion (fun x => hamming_ball c x) ∪ hamming_ring c c' x₀).card =
        Fintype.card (Fin n → Fin q) := by
      rw [Finset.card_union_of_disjoint hdisjAB, hcardA, hring, hcount]
      simp
    have hUuniv : C.biUnion (fun x => hamming_ball c x) ∪ hamming_ring c c' x₀ = Finset.univ :=
      Finset.eq_univ_of_card _ hUcard
    have hy : y ∈ C.biUnion (fun x => hamming_ball c x) ∪ hamming_ring c c' x₀ := by
      rw [hUuniv]; exact Finset.mem_univ y
    rw [Finset.mem_union, Finset.mem_biUnion] at hy
    exact hy
  · have hcc'' : n < c + c' := not_le.mp hcc'
    have hball_c : ∀ x : Fin n → Fin q,
        (hamming_ball c x).card = ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i :=
      fun x => card_hamming_ball n q c hq2 hc_le x
    have hdist_le : ∀ z : Fin n → Fin q, hammingDist x₀ z ≤ n :=
      fun z => by simpa using hammingDist_le_card_fintype (x := x₀) (y := z)
    have hring_eq : hamming_ring c c' x₀ = Finset.univ \ hamming_ball c x₀ := by
      ext z
      have hd : hammingDist x₀ z ≤ n := hdist_le z
      simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        hamming_ball]
      constructor
      · rintro ⟨h1, -⟩; omega
      · intro h; omega
    have hcardB : (hamming_ring c c' x₀).card =
        q ^ n - ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i := by
      rw [hring_eq, Finset.card_sdiff, Finset.inter_univ, hball_c x₀]
      simp
    have hball_pos : 0 < ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i := by
      rw [← hball_c x₀]
      exact Finset.card_pos.mpr ⟨x₀, by simp [hamming_ball]⟩
    have hSle : ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i ≤ q ^ n := by
      rw [← hball_c x₀]
      calc (hamming_ball c x₀).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = q ^ n := by simp
    have hcardA : (C.biUnion (fun x => hamming_ball c x)).card =
        C.card * ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i := by
      rw [Finset.card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun x _ => hball_c x), Finset.sum_const, Nat.nsmul_eq_mul]
    have hdisjAB : Disjoint (C.biUnion (fun x => hamming_ball c x)) (hamming_ring c c' x₀) := by
      rw [Finset.disjoint_biUnion_left]
      exact fun x hx => hdisj_ring x hx x₀ hx₀
    have hle : C.card * (∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i)
        + (q ^ n - ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i) ≤ q ^ n := by
      have h1 : (C.biUnion (fun x => hamming_ball c x) ∪ hamming_ring c c' x₀).card =
          C.card * (∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i)
            + (q ^ n - ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i) := by
        rw [Finset.card_union_of_disjoint hdisjAB, hcardA, hcardB]
      rw [← h1]
      calc (C.biUnion (fun x => hamming_ball c x) ∪ hamming_ring c c' x₀).card
          ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = q ^ n := by simp
    have hCcard_le : C.card ≤ 1 := by
      have hXle : C.card * (∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i) ≤
          1 * ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i := by
        rw [Nat.one_mul]
        have h2 : C.card * (∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i)
              + (q ^ n - ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i)
              + ∑ i ∈ Finset.range (c + 1), n.choose i * (q - 1) ^ i ≤ q ^ n + _ :=
          Nat.add_le_add_right hle _
        rw [Nat.add_assoc, Nat.sub_add_cancel hSle, Nat.add_comm (q ^ n)] at h2
        exact (Nat.add_le_add_iff_right).mp h2
      exact Nat.le_of_mul_le_mul_right hXle hball_pos
    have hk : C.card = 1 := by
      have hpos : 0 < C.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
      omega
    have hCsing : C = {x₀} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hk
      have hxx : x₀ = x := by simpa [hx] using hx₀
      rw [hx, ← hxx]
    by_cases hyc : hammingDist x₀ y ≤ c
    · refine Or.inl ⟨x₀, ?_, ?_⟩
      · rw [hCsing]; simp
      · simpa [hamming_ball] using hyc
    · refine Or.inr ?_
      simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and]
      have hd : hammingDist x₀ y ≤ n := hdist_le y
      omega
