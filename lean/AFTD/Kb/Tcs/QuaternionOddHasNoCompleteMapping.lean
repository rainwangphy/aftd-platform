import AFTD.Prelude
import AFTD.Kb.Tcs.GroupIsCompleteMapping
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.V

/-!
# quaternion_odd_has_no_complete_mapping

Topic: combinatorics   Node: 1c6d4d2d6f08

Provenance: formalization of a published result. Source: arXiv:2611.13274 Cor. 3.21

For every natural number n, the generalized quaternion group QuaternionGroup (2 * n + 1) has no complete mapping.
-/

private lemma quaternion_odd_has_no_complete_mapping_prod_eq_one
    {G A : Type*} [Group G] [Fintype G] [CommGroup A]
    (θ : G → G) (hθ : group_is_complete_mapping θ) (φ : G →* A) :
    ∏ g, φ g = 1 := by
  obtain ⟨h1, h2⟩ := hθ
  have e1 : ∏ g, φ (θ g) = ∏ g, φ g :=
    Fintype.prod_bijective θ h1 (fun x => φ (θ x)) φ (fun x => rfl)
  have e2 : ∏ g, φ (g * θ g) = ∏ g, φ g :=
    Fintype.prod_bijective (fun g => g * θ g) h2 (fun x => φ (x * θ x)) φ (fun x => rfl)
  have e3 : ∏ g, φ (g * θ g) = (∏ g, φ g) * (∏ g, φ (θ g)) := by
    simp only [map_mul]
    exact Finset.prod_mul_distrib
  rw [e2, e1] at e3
  have := congr_arg (· * (∏ g, φ g)⁻¹) e3
  simpa [mul_assoc] using this.symm

private lemma quaternion_odd_has_no_complete_mapping_toAdd_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Multiplicative (ZMod 4)) :
    (s.prod f).toAdd = s.sum (fun i => (f i).toAdd) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    show (f a).toAdd + (s.prod f).toAdd = (f a).toAdd + ∑ i ∈ s, (f i).toAdd
    rw [ih]

private def quaternion_odd_has_no_complete_mapping_equiv (m : ℕ) :
    QuaternionGroup m ≃ ZMod (2*m) ⊕ ZMod (2*m) where
  toFun
    | .a i => Sum.inl i
    | .xa i => Sum.inr i
  invFun
    | Sum.inl i => .a i
    | Sum.inr i => .xa i
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro (i | i) <;> rfl

noncomputable def quaternion_odd_has_no_complete_mapping_mulTwo (n : ℕ) :
    ZMod (2*(2*n+1)) →+ ZMod 4 :=
  ZMod.lift (2*(2*n+1)) ⟨(2:ℕ) • Int.castAddHom (ZMod 4), by
    rw [AddMonoidHom.smul_apply]
    change (2:ℕ) • ((((2*(2*n+1) : ℕ)) : ℤ) : ZMod 4) = 0
    rw [Int.cast_natCast]
    push_cast
    rw [nsmul_eq_mul]
    rw [show ((2:ℕ):ZMod 4) = (2:ZMod 4) from by norm_num]
    rw [show (2:ZMod 4) * (2 * (2 * (↑n : ZMod 4) + 1)) = 4 * (2*(↑n : ZMod 4)+1) from by ring]
    rw [show (4:ZMod 4) = 0 from ZMod.natCast_self 4]
    ring⟩

private lemma quaternion_odd_has_no_complete_mapping_mulTwo_apply (n : ℕ)
    (i : ZMod (2*(2*n+1))) :
    quaternion_odd_has_no_complete_mapping_mulTwo n i = 2 * ((i.val : ℕ) : ZMod 4) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  unfold quaternion_odd_has_no_complete_mapping_mulTwo
  rw [← Int.cast_natCast (R := ZMod (2*(2*n+1)))]
  rw [ZMod.lift_coe]
  change (2 : ℕ) • (((i.val : ℤ)) : ZMod 4) = 2 * ((i.val : ℕ) : ZMod 4)
  rw [nsmul_eq_mul]
  push_cast
  ring

private lemma quaternion_odd_has_no_complete_mapping_mulTwo_add_self (n : ℕ)
    (i : ZMod (2*(2*n+1))) :
    quaternion_odd_has_no_complete_mapping_mulTwo n i +
      quaternion_odd_has_no_complete_mapping_mulTwo n i = 0 := by
  rw [show quaternion_odd_has_no_complete_mapping_mulTwo n i = 2 * ((i.val : ℕ) : ZMod 4)
    from quaternion_odd_has_no_complete_mapping_mulTwo_apply n i]
  rw [show (2 * ((i.val : ℕ) : ZMod 4)) + (2 * ((i.val : ℕ) : ZMod 4))
      = 4 * ((i.val : ℕ) : ZMod 4) from by ring]
  rw [show (4:ZMod 4) = 0 from ZMod.natCast_self 4]
  ring

private lemma quaternion_odd_has_no_complete_mapping_mulTwo_m (n : ℕ) :
    quaternion_odd_has_no_complete_mapping_mulTwo n ((2*n+1 : ℕ) : ZMod (2*(2*n+1))) = 2 := by
  rw [show (((2*n+1 : ℕ)) : ZMod (2*(2*n+1))) = (((2*n+1 : ℤ)) : ZMod (2*(2*n+1)))
    from by push_cast; ring]
  unfold quaternion_odd_has_no_complete_mapping_mulTwo
  rw [ZMod.lift_coe]
  change (2:ℕ) • (((2*n+1 : ℤ)) : ZMod 4) = 2
  rw [nsmul_eq_mul]
  push_cast
  rw [show (2:ZMod 4) * (2 * (↑n : ZMod 4) + 1) = 4 * (↑n : ZMod 4) + 2 from by ring]
  rw [show (4:ZMod 4) = 0 from ZMod.natCast_self 4]
  ring

noncomputable def quaternion_odd_has_no_complete_mapping_hom (n : ℕ) :
    QuaternionGroup (2*n+1) →* Multiplicative (ZMod 4) where
  toFun
    | .a i => Multiplicative.ofAdd (quaternion_odd_has_no_complete_mapping_mulTwo n i)
    | .xa i => Multiplicative.ofAdd (1 + quaternion_odd_has_no_complete_mapping_mulTwo n i)
  map_one' := by
    change Multiplicative.ofAdd (quaternion_odd_has_no_complete_mapping_mulTwo n 0) =
      (1 : Multiplicative (ZMod 4))
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
        QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
    · rw [map_add]
      rfl
    · apply Multiplicative.ext
      change 1 + quaternion_odd_has_no_complete_mapping_mulTwo n (j - i) =
        quaternion_odd_has_no_complete_mapping_mulTwo n i +
          (1 + quaternion_odd_has_no_complete_mapping_mulTwo n j)
      rw [map_sub]
      have hneg : - quaternion_odd_has_no_complete_mapping_mulTwo n i =
          quaternion_odd_has_no_complete_mapping_mulTwo n i :=
        neg_eq_of_add_eq_zero_right (quaternion_odd_has_no_complete_mapping_mulTwo_add_self n i)
      rw [sub_eq_add_neg, hneg]
      ring
    · apply Multiplicative.ext
      change 1 + quaternion_odd_has_no_complete_mapping_mulTwo n (i + j) =
        (1 + quaternion_odd_has_no_complete_mapping_mulTwo n i) +
          quaternion_odd_has_no_complete_mapping_mulTwo n j
      rw [map_add]
      ring
    · apply Multiplicative.ext
      change quaternion_odd_has_no_complete_mapping_mulTwo n ((2*n+1 : ℕ) + j - i) =
        (1 + quaternion_odd_has_no_complete_mapping_mulTwo n i) +
          (1 + quaternion_odd_has_no_complete_mapping_mulTwo n j)
      rw [map_sub, map_add, quaternion_odd_has_no_complete_mapping_mulTwo_m]
      have hneg : - quaternion_odd_has_no_complete_mapping_mulTwo n i =
          quaternion_odd_has_no_complete_mapping_mulTwo n i :=
        neg_eq_of_add_eq_zero_right (quaternion_odd_has_no_complete_mapping_mulTwo_add_self n i)
      rw [sub_eq_add_neg, hneg]
      ring

private lemma quaternion_odd_has_no_complete_mapping_sum (n : ℕ) :
    ∑ g : QuaternionGroup (2*n+1),
      (quaternion_odd_has_no_complete_mapping_hom n g).toAdd = 2 := by
  have heq : (∑ x : ZMod (2*(2*n+1)) ⊕ ZMod (2*(2*n+1)),
      (quaternion_odd_has_no_complete_mapping_hom n
        ((quaternion_odd_has_no_complete_mapping_equiv (2*n+1)).symm x)).toAdd)
      = ∑ g : QuaternionGroup (2*n+1),
          (quaternion_odd_has_no_complete_mapping_hom n g).toAdd :=
    Fintype.sum_equiv (quaternion_odd_has_no_complete_mapping_equiv (2*n+1)).symm _ _
      (fun x => rfl)
  rw [← heq]
  rw [Fintype.sum_sum_type]
  have h1 : ∀ i : ZMod (2*(2*n+1)),
      (quaternion_odd_has_no_complete_mapping_hom n
        ((quaternion_odd_has_no_complete_mapping_equiv (2*n+1)).symm (Sum.inl i))).toAdd
      = quaternion_odd_has_no_complete_mapping_mulTwo n i := fun i => rfl
  have h2 : ∀ i : ZMod (2*(2*n+1)),
      (quaternion_odd_has_no_complete_mapping_hom n
        ((quaternion_odd_has_no_complete_mapping_equiv (2*n+1)).symm (Sum.inr i))).toAdd
      = 1 + quaternion_odd_has_no_complete_mapping_mulTwo n i := fun i => rfl
  simp only [h1, h2]
  have hV : ∑ i : ZMod (2*(2*n+1)), quaternion_odd_has_no_complete_mapping_mulTwo n i
      = 2 * ∑ i : ZMod (2*(2*n+1)), ((i.val : ℕ) : ZMod 4) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ =>
      quaternion_odd_has_no_complete_mapping_mulTwo_apply n i)
  have hC : ∑ i : ZMod (2*(2*n+1)),
        (1 + quaternion_odd_has_no_complete_mapping_mulTwo n i)
      = ((2*(2*n+1) : ℕ) : ZMod 4) +
        ∑ i : ZMod (2*(2*n+1)), quaternion_odd_has_no_complete_mapping_mulTwo n i := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [hC, hV]
  generalize (∑ i : ZMod (2*(2*n+1)), ((i.val : ℕ) : ZMod 4)) = V
  have hc : ((2*(2*n+1) : ℕ) : ZMod 4) = 2 := by
    have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
    push_cast
    rw [show (2:ZMod 4) * (2 * (↑n : ZMod 4) + 1) = 4 * (↑n : ZMod 4) + 2 from by ring, h4]
    ring
  rw [hc]
  rw [show 2 * V + (2 + 2 * V) = 2 from by
    have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
    rw [show 2 * V + (2 + 2 * V) = 4 * V + 2 from by ring]
    rw [show (4:ZMod 4) * V = 0 from by rw [h4, zero_mul]]
    ring]

/-- The generalized quaternion group QuaternionGroup (2 * n + 1) does not admit a complete mapping. -/
theorem quaternion_odd_has_no_complete_mapping (n : ℕ) :
    ¬ ∃ θ : QuaternionGroup (2 * n + 1) → QuaternionGroup (2 * n + 1),
      group_is_complete_mapping θ := by
  rintro ⟨θ, hθ⟩
  have hprod := quaternion_odd_has_no_complete_mapping_prod_eq_one θ hθ
    (quaternion_odd_has_no_complete_mapping_hom n)
  have hsum : (∏ g, quaternion_odd_has_no_complete_mapping_hom n g).toAdd = 0 := by
    rw [hprod]
    rfl
  rw [quaternion_odd_has_no_complete_mapping_toAdd_prod,
    quaternion_odd_has_no_complete_mapping_sum] at hsum
  exact absurd hsum (by decide)
