import AFTD.Prelude
import AFTD.Kb.Tcs.QaryMultipleDeletionHinge
import AFTD.Kb.Tcs.QaryAllZeroWord
import AFTD.Kb.Tcs.QaryConstantWordDeletionEnvelope
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings
import AFTD.Kb.Tcs.G

/-!
# op_1534_constant_word_deletion_envelope_eq

Topic: information   Node: a22d20d534da

Provenance: formalization of a published result. Source: arXiv:2407.10026 "Conditional entropies of k-deletion/insertion channels"

For integers t ≥ 1, q ≥ 2, and n ≥ 1, and any threshold r, the t-deletion hinge sum of the all-zero word qary_all_zero_word q n (by omega) equals the closed-form upper envelope qary_constant_word_deletion_envelope t q n r.
-/

open Finset

private def op_1534_constant_word_deletion_envelope_eq_zset {N q : ℕ} (x : Fin N → Fin q) (z0 : Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun j => x j = z0)

private noncomputable def op_1534_constant_word_deletion_envelope_eq_zset_equiv {N q : ℕ} (z0 : Fin q) (S : Finset (Fin N)) :
    {x : Fin N → Fin q // op_1534_constant_word_deletion_envelope_eq_zset x z0 = S} ≃ ({j : Fin N // j ∉ S} → {v : Fin q // v ≠ z0}) where
  toFun x := fun j => ⟨x.1 j.1, by
      intro h
      have hj : j.1 ∈ op_1534_constant_word_deletion_envelope_eq_zset x.1 z0 := by simp [op_1534_constant_word_deletion_envelope_eq_zset, h]
      rw [x.2] at hj
      exact j.2 hj⟩
  invFun g := ⟨fun j => if h : j ∈ S then z0 else (g ⟨j, h⟩).1, by
      ext j
      simp only [op_1534_constant_word_deletion_envelope_eq_zset, mem_filter, mem_univ, true_and]
      by_cases h : j ∈ S
      · rw [dif_pos h]; exact iff_of_true rfl h
      · rw [dif_neg h]
        exact iff_of_false (g ⟨j, h⟩).2 h⟩
  left_inv := by
    intro x
    ext j
    by_cases h : j ∈ S
    · have hx : x.1 j = z0 := by
        have : j ∈ op_1534_constant_word_deletion_envelope_eq_zset x.1 z0 := by rw [x.2]; exact h
        simpa [op_1534_constant_word_deletion_envelope_eq_zset] using this
      simp [h, hx]
    · simp [h]
  right_inv := by
    intro g
    ext j
    simp only [dif_neg j.2]

private theorem op_1534_constant_word_deletion_envelope_eq_card_zset_fiber {N q : ℕ} (z0 : Fin q) (S : Finset (Fin N)) :
    Fintype.card {x : Fin N → Fin q // op_1534_constant_word_deletion_envelope_eq_zset x z0 = S} = (q - 1) ^ (N - S.card) := by
  rw [Fintype.card_congr (op_1534_constant_word_deletion_envelope_eq_zset_equiv z0 S), Fintype.card_fun]
  have h1 : Fintype.card {j : Fin N // j ∉ S} = N - S.card := by
    rw [Fintype.card_subtype]
    have hh : ({x : Fin N | x ∉ S} : Finset (Fin N)) = Sᶜ := by ext x; simp
    rw [hh, Finset.card_compl, Fintype.card_fin]
  have h2 : Fintype.card {v : Fin q // v ≠ z0} = q - 1 := by
    rw [Fintype.card_subtype]
    have hh : ({v : Fin q | v ≠ z0} : Finset (Fin q)) = (univ : Finset (Fin q)).erase z0 := by
      ext v; simp
    rw [hh, Finset.card_erase_of_mem (Finset.mem_univ z0), Finset.card_univ, Fintype.card_fin]
  rw [h1, h2]

private theorem op_1534_constant_word_deletion_envelope_eq_card_zcount_fiber {N q : ℕ} (z0 : Fin q) (z : ℕ) :
    (Finset.univ.filter (fun x : Fin N → Fin q => (op_1534_constant_word_deletion_envelope_eq_zset x z0).card = z)).card
      = N.choose z * (q - 1) ^ (N - z) := by
  have hmap : Set.MapsTo (fun x : Fin N → Fin q => op_1534_constant_word_deletion_envelope_eq_zset x z0)
      ↑(Finset.univ.filter (fun x : Fin N → Fin q => (op_1534_constant_word_deletion_envelope_eq_zset x z0).card = z))
      ↑((univ : Finset (Fin N)).powersetCard z) := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hx⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hterm : ∀ b ∈ (univ : Finset (Fin N)).powersetCard z,
      {a ∈ Finset.univ.filter (fun x : Fin N → Fin q => (op_1534_constant_word_deletion_envelope_eq_zset x z0).card = z) | op_1534_constant_word_deletion_envelope_eq_zset a z0 = b}.card
        = (q - 1) ^ (N - z) := by
    intro b hb
    rw [Finset.mem_powersetCard] at hb
    obtain ⟨-, hbc⟩ := hb
    have heq : {a ∈ Finset.univ.filter (fun x : Fin N → Fin q => (op_1534_constant_word_deletion_envelope_eq_zset x z0).card = z) | op_1534_constant_word_deletion_envelope_eq_zset a z0 = b}
        = Finset.univ.filter (fun a : Fin N → Fin q => op_1534_constant_word_deletion_envelope_eq_zset a z0 = b) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact hbc, h⟩
    rw [heq, ← Fintype.card_subtype, op_1534_constant_word_deletion_envelope_eq_card_zset_fiber, hbc]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

private theorem op_1534_constant_word_deletion_envelope_eq_card_embeddings {n N q : ℕ} (z0 : Fin q) (x : Fin N → Fin q) :
    q_ary_subsequence_num_embeddings q n N (fun _ => z0) x = (op_1534_constant_word_deletion_envelope_eq_zset x z0).card.choose n := by
  rw [q_ary_subsequence_num_embeddings]
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun f _ => Finset.image f Finset.univ)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hmono, hval⟩ := hf
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, -, rfl⟩ := hj
      simp only [op_1534_constant_word_deletion_envelope_eq_zset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hval i
    · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro f1 hf1 f2 hf2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf1 hf2
    have hc : (Finset.image f1 Finset.univ).card = n := by
      rw [Finset.card_image_of_injective _ hf1.1.injective, Finset.card_univ, Fintype.card_fin]
    have e1 := Finset.orderEmbOfFin_unique hc
      (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) hf1.1
    have e2 := Finset.orderEmbOfFin_unique hc
      (fun i => by rw [heq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)) hf2.1
    exact e1.trans e2.symm
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hsub, hcard⟩ := hS
    refine ⟨⇑(S.orderEmbOfFin hcard), ?_, Finset.image_orderEmbOfFin_univ S hcard⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(S.orderEmbOfFin hcard).strictMono, fun i => ?_⟩
    simpa only [op_1534_constant_word_deletion_envelope_eq_zset, Finset.mem_filter, Finset.mem_univ, true_and] using
      hsub (Finset.orderEmbOfFin_mem S hcard i)

/-- The multiple-deletion hinge sum of the all-zero word matches the explicit upper envelope. -/
theorem op_1534_constant_word_deletion_envelope_eq
    (t : ℕ) (ht : 1 ≤ t) (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 1 ≤ n)
    (r : ℕ) :
    qary_multiple_deletion_hinge t q n r (qary_all_zero_word q n (by omega)) =
      qary_constant_word_deletion_envelope t q n r := by
  rw [qary_multiple_deletion_hinge, qary_constant_word_deletion_envelope]
  set z0 : Fin q := ⟨0, by omega⟩ with hz0
  have hzw : qary_all_zero_word q n (by omega) = (fun _ : Fin n => z0) := rfl
  rw [hzw]
  have hstep : ∀ x : Fin (n + t) → Fin q,
      q_ary_subsequence_num_embeddings q n (n + t) (fun _ => z0) x
        = (op_1534_constant_word_deletion_envelope_eq_zset x z0).card.choose n :=
    fun x => op_1534_constant_word_deletion_envelope_eq_card_embeddings z0 x
  have hmap : ∀ x ∈ (Finset.univ : Finset (Fin (n + t) → Fin q)),
      (op_1534_constant_word_deletion_envelope_eq_zset x z0).card ∈ Finset.range (n + t + 1) := by
    intro x _
    rw [Finset.mem_range]
    have h1 : op_1534_constant_word_deletion_envelope_eq_zset x z0 ⊆ (Finset.univ : Finset (Fin (n + t))) :=
      Finset.filter_subset _ _
    have h2 := Finset.card_le_card h1
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  calc ∑ x : Fin (n + t) → Fin q, (q_ary_subsequence_num_embeddings q n (n + t) (fun _ => z0) x - r)
      = ∑ x : Fin (n + t) → Fin q, ((op_1534_constant_word_deletion_envelope_eq_zset x z0).card.choose n - r) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hstep x]
    _ = ∑ z ∈ Finset.range (n + t + 1),
          ∑ x ∈ Finset.univ.filter (fun x : Fin (n + t) → Fin q => (op_1534_constant_word_deletion_envelope_eq_zset x z0).card = z),
            (z.choose n - r) := by
        exact (Finset.sum_fiberwise_of_maps_to' hmap (fun z => z.choose n - r)).symm
    _ = ∑ z ∈ Finset.range (n + t + 1),
          (((n + t).choose z * (q - 1) ^ (n + t - z)) * (z.choose n - r)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_const, op_1534_constant_word_deletion_envelope_eq_card_zcount_fiber, Nat.nsmul_eq_mul]
    _ = ∑ z ∈ Finset.Icc n (n + t), ((n + t).choose z * (q - 1) ^ (n + t - z) * (z.choose n - r)) := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro z hz
          rw [Finset.mem_Icc] at hz
          rw [Finset.mem_range]
          omega
        · intro z hz hznot
          rw [Finset.mem_range] at hz
          rw [Finset.mem_Icc] at hznot
          have hlt : z < n := by omega
          rw [Nat.choose_eq_zero_of_lt hlt]
          simp
