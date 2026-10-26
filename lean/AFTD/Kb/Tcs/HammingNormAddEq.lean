import AFTD.Prelude

/-!
# hamming_norm_add_eq

Topic: information   Node: a3643c760f46

Provenance: helper lemma. arXiv:2610.29807, Lemma 3.2: Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

For any finite type α and any two Boolean functions f, g : α → ZMod 2, the Hamming norm of their pointwise sum f + g equals hammingNorm f + hammingNorm g - 2 * hammingNorm (f * g).
-/

lemma hamming_norm_add_eq_zmod2_add (x y : ZMod 2) :
    (x + y ≠ 0) ↔ (x ≠ 0 ∧ y = 0) ∨ (x = 0 ∧ y ≠ 0) := by
  revert x y
  decide

lemma hamming_norm_add_eq_zmod2_mul (x y : ZMod 2) :
    (x * y ≠ 0) ↔ (x ≠ 0 ∧ y ≠ 0) := by
  revert x y
  decide

/-- Inclusion-exclusion for the Hamming norm of the sum of two Boolean functions. -/
theorem hamming_norm_add_eq {α : Type*} [Fintype α]
    (f g : α → ZMod 2) :
    hammingNorm (f + g) = hammingNorm f + hammingNorm g - 2 * hammingNorm (f * g) := by
  classical
  let s : Finset α := Finset.univ.filter (fun i => f i ≠ 0)
  let t : Finset α := Finset.univ.filter (fun i => g i ≠ 0)
  have h_add_set : Finset.univ.filter (fun i => (f + g) i ≠ 0) = symmDiff s t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
      Pi.add_apply, hamming_norm_add_eq_zmod2_add, s, t, not_not]
    tauto
  have h_mul_set : Finset.univ.filter (fun i => (f * g) i ≠ 0) = s ∩ t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Pi.mul_apply, hamming_norm_add_eq_zmod2_mul, s, t]
  have h_card : (symmDiff s t).card = s.card + t.card - 2 * (s ∩ t).card := by
    have h1 : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
      rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have h2 := Finset.card_sdiff_add_card_inter s t
    have h3 := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm t s] at h3
    omega
  change (Finset.univ.filter (fun i => (f + g) i ≠ 0)).card =
    s.card + t.card - 2 * (Finset.univ.filter (fun i => (f * g) i ≠ 0)).card
  rw [h_add_set, h_mul_set]
  exact h_card
