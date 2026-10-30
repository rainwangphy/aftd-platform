import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointFirstBlock

/-!
# wild_joint_first_block_fiber_mass

Topic: graphs   Node: 579e47139915

Provenance: helper lemma. IN-382 / OP-306 campaign9. Explicit residual finite-counting tasks for wild_joint_expected_ID_eq_alpha_sum; no wild-number advance is claimed.

For any three-element T on Fin(3q), q>=3, the number of vertex permutations with first block T times choose(3q,3) equals the number of all vertex permutations.
-/

open Finset

noncomputable def wild_joint_first_block_fiber_mass_equiv_of_card_eq {α : Type*} [DecidableEq α] [Fintype α]
    (s t : Finset α) (h : s.card = t.card) : Equiv.Perm α :=
  let e1 : (s : Set α) ≃ (t : Set α) :=
    Fintype.equivOfCardEq (by simp [h])
  have hcompl : Fintype.card ((s : Set α)ᶜ : Set α) = Fintype.card ((t : Set α)ᶜ : Set α) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set]
    simp [h]
  let e2 : ((s : Set α)ᶜ : Set α) ≃ ((t : Set α)ᶜ : Set α) :=
    Fintype.equivOfCardEq hcompl
  (Equiv.Set.sumCompl (s : Set α)).symm.trans
    ((e1.sumCongr e2).trans (Equiv.Set.sumCompl (t : Set α)))

lemma wild_joint_first_block_fiber_mass_equiv_of_card_eq_image {α : Type*} [DecidableEq α] [Fintype α]
    (s t : Finset α) (h : s.card = t.card) :
    s.image (wild_joint_first_block_fiber_mass_equiv_of_card_eq s t h) = t := by
  ext x
  simp only [wild_joint_first_block_fiber_mass_equiv_of_card_eq, Equiv.trans_apply, Equiv.sumCongr_apply, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (s : Set α) := hy
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hy']
    simp only [Sum.map_inl]
    rw [Equiv.Set.sumCompl_apply_inl]
    exact Subtype.mem _
  · intro hx
    have hx' : x ∈ (t : Set α) := hx
    let e1 : (s : Set α) ≃ (t : Set α) :=
      Fintype.equivOfCardEq (by simp [h])
    let y_sub := e1.symm ⟨x, hx'⟩
    refine ⟨y_sub.val, y_sub.property, ?_⟩
    have hy' : y_sub.val ∈ (s : Set α) := y_sub.property
    have hy_eq : (⟨y_sub.val, hy'⟩ : (s : Set α)) = y_sub := Subtype.ext rfl
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hy']
    simp only [Sum.map_inl]
    rw [Equiv.Set.sumCompl_apply_inl]
    change (e1 ⟨y_sub.val, hy'⟩).val = x
    rw [hy_eq, Equiv.apply_symm_apply]

lemma wild_joint_first_block_fiber_mass_card (q : ℕ) (hq : 3 ≤ q) (σ : Equiv.Perm (Fin (3*q))) :
    (wild_joint_first_block q σ).card = 3 := by
  have h0 : 0 < 3 * q := by omega
  have h1 : 1 < 3 * q := by omega
  have h2 : 2 < 3 * q := by omega
  have heq : univ.filter (fun (i : Fin (3*q)) => i.val < 3) =
      {⟨0, h0⟩, ⟨1, h1⟩, ⟨2, h2⟩} := by
    ext ⟨x, hx⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
    omega
  have hcard : (univ.filter (fun (i : Fin (3*q)) => i.val < 3)).card = 3 := by
    rw [heq, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  have himage : wild_joint_first_block q σ =
      (univ.filter (fun (i : Fin (3*q)) => i.val < 3)).image σ := by
    ext x
    simp only [wild_joint_first_block, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      exact ⟨σ.symm x, hx, σ.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [himage, card_image_of_injective _ σ.injective, hcard]

lemma wild_joint_first_block_fiber_mass_fiber_card_eq
    (q : ℕ) (S T : Finset (Fin (3*q))) (e : Equiv.Perm (Fin (3*q)))
    (heT : S.image e = T) :
    (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = S).card =
    (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T).card := by
  have hfirst : ∀ σ : Equiv.Perm (Fin (3*q)),
      wild_joint_first_block q (σ.trans e) = (wild_joint_first_block q σ).image e := by
    intro σ
    ext x
    simp only [wild_joint_first_block, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hfirstiff : ∀ σ : Equiv.Perm (Fin (3*q)),
      wild_joint_first_block q (σ.trans e) = T ↔ wild_joint_first_block q σ = S := by
    intro σ
    rw [hfirst, ← heT]
    exact Finset.image_injective e.injective |>.eq_iff
  apply card_bij (fun σ _ => σ.trans e)
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    exact (hfirstiff σ).mpr hσ
  · intro σ₁ _ σ₂ _ h
    apply Equiv.ext
    intro x
    have hh := congrArg (fun a : Equiv.Perm (Fin (3*q)) => a x) h
    exact e.injective hh
  · intro τ hτ
    have hc : (τ.trans e.symm).trans e = τ := by ext x; simp
    refine ⟨τ.trans e.symm, ?_, hc⟩
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    apply (hfirstiff _).mp
    rw [hc]
    exact hτ

theorem wild_joint_first_block_fiber_mass
    (q : ℕ) (hq : 3 ≤ q) (T : Finset (Fin (3*q))) (hT : T.card = 3) :
    (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T).card *
      (3*q).choose 3 = Fintype.card (Equiv.Perm (Fin (3*q))) := by
  classical
  have hmaps : Set.MapsTo (wild_joint_first_block q) (↑(univ : Finset (Equiv.Perm (Fin (3*q)))))
      (↑(powersetCard 3 (univ : Finset (Fin (3*q))))) := by
    intro σ _
    simp only [mem_coe, mem_powersetCard_univ]
    exact wild_joint_first_block_fiber_mass_card q hq σ
  have hsum := card_eq_sum_card_fiberwise (f := wild_joint_first_block q)
    (s := (univ : Finset (Equiv.Perm (Fin (3*q))))) (t := powersetCard 3 univ) hmaps
  have hterm : ∀ b ∈ powersetCard 3 (univ : Finset (Fin (3*q))),
      {a ∈ (univ : Finset (Equiv.Perm (Fin (3*q)))) | wild_joint_first_block q a = b}.card =
      (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T).card := by
    intro b hb
    rw [mem_powersetCard_univ] at hb
    have he : b.image (wild_joint_first_block_fiber_mass_equiv_of_card_eq b T (by rw [hb, hT])) = T :=
      wild_joint_first_block_fiber_mass_equiv_of_card_eq_image b T (by rw [hb, hT])
    have heq := wild_joint_first_block_fiber_mass_fiber_card_eq q b T _ he
    have hfilter : {a ∈ (univ : Finset (Equiv.Perm (Fin (3*q)))) | wild_joint_first_block q a = b} =
        univ.filter (fun σ => wild_joint_first_block q σ = b) := by
      ext; simp
    rw [hfilter, heq]
  rw [sum_congr rfl hterm] at hsum
  simp only [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [mul_comm, hsum]
