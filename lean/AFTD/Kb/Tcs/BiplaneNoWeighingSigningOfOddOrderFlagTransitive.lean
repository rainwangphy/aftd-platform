import AFTD.Prelude
import AFTD.Kb.Tcs.BiplaneWeighingSigning
import AFTD.Kb.Tcs.BiplaneAutomorphismGroup
import AFTD.Kb.Tcs.BiplaneFlagMulAction
import AFTD.Kb.Tcs.Biplane
import AFTD.Kb.Tcs.BiplaneFlag
import AFTD.Kb.Tcs.C

/-!
# biplane_no_weighing_signing_of_odd_order_flag_transitive

Topic: combinatorics   Node: 6472b04bc491

Provenance: formalization of a published result. Source: arXiv:2611.17855 (On configurations that are nearly generalised polygons), Proposition 2.11. Extra hypothesis: at least two lines. The knowledge-base Biplane axioms also admit the degenerate one-point, one-line structure with k = 1, which has a weighing signing and a trivial flag-transitive group, so the proposition needs the hypothesis there; every biplane in the paper's sense has v ≥ 4.

Let B be a biplane (a symmetric 2-(v, k, 2) design, with points P and lines L) having at least two distinct lines. If some subgroup G of the automorphism group of B has odd order and acts transitively on the flags of B, then B admits no weighing signing.
-/

open Classical in
theorem bpws_pair_prod {P L : Type*} [Fintype P] [Fintype L] (B : Biplane P L)
    (σ : BiplaneFlag B → ℤ) (hσ : biplane_weighing_signing B σ)
    (l1 l2 : L) (hl : l1 ≠ l2) (p1 p2 : P) (hp : p1 ≠ p2) (h11 : B.inc p1 l1)
    (h12 : B.inc p1 l2) (h21 : B.inc p2 l1) (h22 : B.inc p2 l2) :
    σ ⟨(p1, l1), h11⟩ * σ ⟨(p1, l2), h12⟩ * (σ ⟨(p2, l1), h21⟩ * σ ⟨(p2, l2), h22⟩) = -1 := by
  have hE := congrFun (congrFun hσ.2 l1) l2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply_ne hl, smul_zero] at hE
  have hcommon : ∀ p, B.inc p l1 → B.inc p l2 → p = p1 ∨ p = p2 := by
    intro p hpl1 hpl2
    by_contra hne
    push_neg at hne
    have hc := B.lines_inter_two l1 l2 hl
    rw [Nat.card_eq_fintype_card] at hc
    have h3 : ({⟨p1, h11, h12⟩, ⟨p2, h21, h22⟩, ⟨p, hpl1, hpl2⟩} :
        Finset {q : P // B.inc q l1 ∧ B.inc q l2}).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h; exact hne.2 (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hp (congrArg Subtype.val h), fun h => hne.1 (congrArg Subtype.val h).symm⟩
    have := Finset.card_le_univ ({⟨p1, h11, h12⟩, ⟨p2, h21, h22⟩, ⟨p, hpl1, hpl2⟩} :
        Finset {q : P // B.inc q l1 ∧ B.inc q l2})
    omega
  rw [Fintype.sum_eq_add p1 p2 hp] at hE
  · simp only [dif_pos h11, dif_pos h12, dif_pos h21, dif_pos h22] at hE
    rcases hσ.1 ⟨(p1, l1), h11⟩ with a | a <;> rcases hσ.1 ⟨(p1, l2), h12⟩ with b | b <;>
      rcases hσ.1 ⟨(p2, l1), h21⟩ with c | c <;> rcases hσ.1 ⟨(p2, l2), h22⟩ with d | d <;>
      (rw [a, b, c, d] at hE ⊢) <;> (try norm_num at hE) <;> (try norm_num)
  · intro x hx
    by_cases hx1 : B.inc x l1
    · by_cases hx2 : B.inc x l2
      · rcases hcommon x hx1 hx2 with h | h
        · exact absurd h hx.1
        · exact absurd h hx.2
      · rw [dif_neg hx2, mul_zero]
    · rw [dif_neg hx1, zero_mul]

theorem biplane_no_weighing_signing_of_odd_order_flag_transitive {P L : Type*} [Fintype P]
    [Fintype L] (B : Biplane P L) (hL : ∃ l₁ l₂ : L, l₁ ≠ l₂)
    (G : Subgroup (biplane_automorphism_group B))
    (hodd : Odd (Nat.card G)) (htrans : MulAction.IsPretransitive G (BiplaneFlag B)) :
    ¬ ∃ σ : BiplaneFlag B → ℤ, biplane_weighing_signing B σ := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l1, l2, hl⟩ := hL
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, hne, -⟩ := Nat.card_eq_two_iff.1 (B.lines_inter_two l1 l2 hl)
  have hp : p1 ≠ p2 := fun h => hne (Subtype.ext h)
  haveI : Fintype G := Fintype.ofFinite G
  let τ : BiplaneFlag B → ℤ := fun f => ∏ g : G, σ (g • f)
  have hconst : ∀ f f' : BiplaneFlag B, τ f = τ f' := by
    intro f f'
    obtain ⟨h, rfl⟩ := htrans.exists_smul_eq f f'
    show ∏ g : G, σ (g • f) = ∏ g : G, σ (g • h • f)
    refine Fintype.prod_equiv (Equiv.mulRight h⁻¹) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, mul_smul, inv_smul_smul]
  have hval : ∀ f, τ f = 1 ∨ τ f = -1 := by
    intro f
    classical
    have : ∀ s : Finset G, ∏ g ∈ s, σ (g • f) = 1 ∨ ∏ g ∈ s, σ (g • f) = -1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        rcases hσ.1 (a • f) with h1 | h1 <;> rcases ih with h2 | h2 <;> rw [h1, h2] <;> norm_num
    exact this Finset.univ
  let f11 : BiplaneFlag B := ⟨(p1, l1), hp1.1⟩
  let f12 : BiplaneFlag B := ⟨(p1, l2), hp1.2⟩
  let f21 : BiplaneFlag B := ⟨(p2, l1), hp2.1⟩
  let f22 : BiplaneFlag B := ⟨(p2, l2), hp2.2⟩
  have hprod : τ f11 * τ f12 * (τ f21 * τ f22) = -1 := by
    show (∏ g : G, σ (g • f11)) * (∏ g : G, σ (g • f12)) *
      ((∏ g : G, σ (g • f21)) * (∏ g : G, σ (g • f22))) = -1
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have hg : ∀ g : G, σ (g • f11) * σ (g • f12) * (σ (g • f21) * σ (g • f22)) = -1 := by
      intro g
      exact bpws_pair_prod B σ hσ ((g : biplane_automorphism_group B).1.2 l1)
        ((g : biplane_automorphism_group B).1.2 l2)
        (fun h => hl ((g : biplane_automorphism_group B).1.2.injective h))
        ((g : biplane_automorphism_group B).1.1 p1) ((g : biplane_automorphism_group B).1.1 p2)
        (fun h => hp ((g : biplane_automorphism_group B).1.1.injective h)) _ _ _ _
    rw [Finset.prod_congr rfl (fun g _ => hg g), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hodd.neg_one_pow]
  rw [hconst f12 f11, hconst f21 f11, hconst f22 f11] at hprod
  rcases hval f11 with h | h <;> rw [h] at hprod <;> norm_num at hprod
