import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CczLayerSyndrome

/-!
# ccz_layer_parity_repr_card_ge

Topic: quantum   Node: 0f553ca81c1b

Provenance: formalization of a published result. Source: arXiv:2610.01024, Corollary 83 (Hadamard-free floor of 6m + 1 for m disjoint CCZ gates)

The Hadamard-free floor of arXiv:2610.01024 (Corollary 83): every set of nonzero parities on 3m qubits whose order-1, 2, 3 moments equal the syndrome of the layer of m >= 1 disjoint CCZ gates has at least 6m + 1 elements; so every Hadamard-free {CNOT, T} circuit for the layer uses at least 6m + 1 T gates.
-/

/-- The CCZ-layer syndrome vanishes on every set that is not of size three. -/
theorem ccz_layer_syndrome_eq_zero_of_card_ne {m : ℕ} (A : Finset (Fin (3 * m)))
    (hA : A.card ≠ 3) : ccz_layer_syndrome m A = 0 := by
  unfold ccz_layer_syndrome
  rw [if_neg]
  rintro ⟨j, rfl⟩
  apply hA
  rw [Finset.card_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp [Fin.ext_iff]

/-- For every qubit `i` of the layer, the two other qubits `p`, `q` of its CCZ block single out
`i`: the syndrome of `{a, p, q}` is `1` exactly when `a = i`. -/
theorem ccz_layer_syndrome_partner {m : ℕ} (i : Fin (3 * m)) :
    ∃ p q : Fin (3 * m), ∀ a, ccz_layer_syndrome m {a, p, q} = if a = i then 1 else 0 := by
  have hi := i.isLt
  refine ⟨⟨3 * (i.val / 3) + (i.val % 3 + 1) % 3, by omega⟩,
    ⟨3 * (i.val / 3) + (i.val % 3 + 2) % 3, by omega⟩, fun a => ?_⟩
  unfold ccz_layer_syndrome
  by_cases hai : a = i
  · subst hai
    rw [if_pos rfl, if_pos]
    refine ⟨⟨a.val / 3, by omega⟩, ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  · rw [if_neg hai, if_neg]
    rintro ⟨j, hj⟩
    have h1 : a ∈ ({a, ⟨3 * (i.val / 3) + (i.val % 3 + 1) % 3, by omega⟩,
        ⟨3 * (i.val / 3) + (i.val % 3 + 2) % 3, by omega⟩} : Finset (Fin (3 * m))) := by simp
    have h2 : (⟨3 * (i.val / 3) + (i.val % 3 + 1) % 3, by omega⟩ : Fin (3 * m)) ∈
        ({a, ⟨3 * (i.val / 3) + (i.val % 3 + 1) % 3, by omega⟩,
        ⟨3 * (i.val / 3) + (i.val % 3 + 2) % 3, by omega⟩} : Finset (Fin (3 * m))) := by simp
    have h3 : (⟨3 * j.val, by omega⟩ : Fin (3 * m)) ∈
        ({⟨3 * j.val, by omega⟩, ⟨3 * j.val + 1, by omega⟩, ⟨3 * j.val + 2, by omega⟩} :
          Finset (Fin (3 * m))) := by simp
    have h4 : (⟨3 * j.val + 1, by omega⟩ : Fin (3 * m)) ∈
        ({⟨3 * j.val, by omega⟩, ⟨3 * j.val + 1, by omega⟩, ⟨3 * j.val + 2, by omega⟩} :
          Finset (Fin (3 * m))) := by simp
    have h5 : (⟨3 * j.val + 2, by omega⟩ : Fin (3 * m)) ∈
        ({⟨3 * j.val, by omega⟩, ⟨3 * j.val + 1, by omega⟩, ⟨3 * j.val + 2, by omega⟩} :
          Finset (Fin (3 * m))) := by simp
    rw [hj] at h1 h2
    rw [← hj] at h3 h4 h5
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h1 h2 h3 h4 h5
    have := Fin.val_ne_of_ne hai
    omega

theorem ccz_layer_parity_repr_card_ge (m : ℕ) (hm : 1 ≤ m) (S : Finset (Finset (Fin (3 * m)))) (hS : is_parity_repr S (ccz_layer_syndrome m)) : 6 * m + 1 ≤ S.card := by
  classical
  -- the incidence matrix of qubits against parities
  let M : Matrix (Fin (3 * m)) S (ZMod 2) := Matrix.of fun a y => if a ∈ (y : Finset _) then 1 else 0
  have hcount : ∀ A : Finset (Fin (3 * m)),
      ((S.filter fun y => A ⊆ y).card : ZMod 2) = ∑ y : S, ∏ a ∈ A, M a y := by
    intro A
    simp only [M, Matrix.of_apply, Finset.prod_boole]
    rw [Finset.natCast_card_filter, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp_all [Finset.subset_iff]
  have hsyn : ∀ A : Finset (Fin (3 * m)), A.Nonempty → A.card ≤ 3 →
      ∑ y : S, ∏ a ∈ A, M a y = ccz_layer_syndrome m A := by
    intro A hA hA3
    rw [← hcount]
    exact hS.2 A ⟨hA.card_pos, hA3⟩
  have hM01 : ∀ a y, M a y * M a y = M a y := by
    intro a y; simp only [M, Matrix.of_apply]; split_ifs <;> simp
  -- order-one and order-two moments vanish
  have h1 : ∀ a, ∑ y : S, M a y = 0 := by
    intro a
    have := hsyn {a} (by simp) (by simp)
    rw [ccz_layer_syndrome_eq_zero_of_card_ne _ (by simp)] at this
    simpa using this
  have h2 : ∀ a b, ∑ y : S, M a y * M b y = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp only [hM01]; exact h1 a
    · have := hsyn {a, b} (by simp) ((Finset.card_le_two).trans (by norm_num))
      rw [ccz_layer_syndrome_eq_zero_of_card_ne _ (by rw [Finset.card_pair hab]; norm_num)] at this
      simpa only [Finset.prod_pair hab] using this
  have h3 : ∀ a b c, ∑ y : S, M a y * M b y * M c y = ccz_layer_syndrome m {a, b, c} := by
    intro a b c
    rw [← hsyn {a, b, c} (by simp) Finset.card_le_three]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [M, Matrix.of_apply, Finset.prod_boole,
      Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    split_ifs <;> simp_all
  -- S is nonempty: the first CCZ triple has odd moment
  have hne : Nonempty S := by
    by_contra hS0
    rw [not_nonempty_iff] at hS0
    have := h3 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    unfold ccz_layer_syndrome at this
    rw [if_pos ⟨⟨0, by omega⟩, by simp⟩] at this
    exact zero_ne_one this
  -- the map (v, λ) ↦ M.transpose v + λ · 1
  let L : (Fin (3 * m) → ZMod 2) × ZMod 2 →ₗ[ZMod 2] (S → ZMod 2) :=
    (Matrix.mulVecLin M.transpose).coprod (LinearMap.smulRight LinearMap.id 1)
  have hL : ∀ v l y, L (v, l) y = (∑ a, M a y * v a) + l := by
    intro v l y
    simp [L, Matrix.vecMul, dotProduct, mul_comm]
  -- evaluating against the two partners of `i` recovers `v i`
  have heval : ∀ v l i, ∃ p q : Fin (3 * m), ∑ y : S, L (v, l) y * M p y * M q y = v i := by
    intro v l i
    obtain ⟨p, q, hpq⟩ := ccz_layer_syndrome_partner i
    refine ⟨p, q, ?_⟩
    simp only [hL, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e1 : ∀ a, ∑ y : S, M a y * v a * M p y * M q y = v a * ccz_layer_syndrome m {a, p, q} := by
      intro a
      rw [← h3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by ring
    have e2 : ∑ y : S, l * M p y * M q y = 0 := by
      rw [← mul_zero l, ← h2 p q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by ring
    simp only [e1, e2, hpq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, add_zero]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨v, l⟩ hvl
    have hv : v = 0 := by
      funext i
      obtain ⟨p, q, h⟩ := heval v l i
      rw [← h, hvl]
      simp
    subst hv
    obtain ⟨y⟩ := hne
    have := congrFun hvl y
    rw [hL] at this
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this
    rw [this]; rfl
  -- the image of L lies in the kernel of M
  have hker : LinearMap.range L ≤ LinearMap.ker M.mulVecLin := by
    rintro x ⟨⟨v, l⟩, rfl⟩
    rw [LinearMap.mem_ker]
    funext b
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hL, Pi.zero_apply, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e1 : ∀ a, ∑ y : S, M b y * (M a y * v a) = 0 := by
      intro a
      rw [← zero_mul (v a), ← h2 b a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    have e2 : ∑ y : S, M b y * l = 0 := by rw [← Finset.sum_mul, h1, zero_mul]
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
  -- dimension count
  have hrankT : M.transpose.rank = 3 * m := by
    have hinj : Function.Injective (Matrix.mulVecLin M.transpose) := by
      intro v w hvw
      have := @hLinj (v, 0) (w, 0) (by simpa [L] using hvw)
      exact (Prod.ext_iff.1 this).1
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have hrank : M.rank = 3 * m := by rw [← Matrix.rank_transpose]; exact hrankT
  have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hmono := Submodule.finrank_mono hker
  rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_self] at hmono
  rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hnull
  omega
