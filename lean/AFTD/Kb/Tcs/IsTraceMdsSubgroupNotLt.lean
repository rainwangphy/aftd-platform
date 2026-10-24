import AFTD.Prelude
import AFTD.Kb.Tcs.IsTraceMdsSubgroup

/-!
# is_trace_mds_subgroup_not_lt

Topic: information   Node: 7284eba9616f

Provenance: helper lemma. step towards subgroup_rigidity_order_of_mds

Under the MDS hypothesis, if x ∈ H has order d > 1 and q^r ≡ 1 (mod d) with r > 0, it cannot be that both r < k and r < d.
-/

/-- Under the MDS condition on H, an element of order d cannot satisfy q^r = 1 with r < k and r < d. -/
theorem is_trace_mds_subgroup_not_lt {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] (q k : ℕ) (H : Subgroup Lˣ) [Fintype H] (hq : Fintype.card F = q) (h_mds : is_trace_mds_subgroup F H k) (x : H) (d : ℕ) (hx : orderOf x = d) (hd : 1 < d) (r : ℕ) (hr_pow : (q : ZMod d) ^ r = 1) (hr_pos : 0 < r) : ¬ (r < k ∧ r < d) := by
  classical
  rintro ⟨hrk, hrd⟩
  -- q is the size of the base field, so `2 ≤ q`
  have hq2 : 2 ≤ q := by rw [← hq]; exact Fintype.one_lt_card
  have hqpos : 0 < q := by omega
  have hqr1 : 1 ≤ q ^ r := Nat.one_le_pow r _ hqpos
  -- `q ^ r ≡ 1 (mod d)` read inside `ZMod d`
  have hqr_cast : ((q ^ r : ℕ) : ZMod d) = 1 := by
    push_cast
    exact hr_pow
  -- hence `d ∣ q ^ r - 1`
  have hdvd : d ∣ q ^ r - 1 := by
    refine (ZMod.natCast_eq_zero_iff (q ^ r - 1) d).mp ?_
    rw [Nat.cast_sub hqr1, hqr_cast]
    simp
  obtain ⟨m, hm⟩ := hdvd
  have hqr_eq : q ^ r = d * m + 1 := by omega
  -- the element `x` of order `d` is fixed by `y ↦ y ^ (q ^ r)`
  have hy_d : ((↑x : Lˣ) : L) ^ d = 1 := by
    have h1 : x ^ d = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h2 : (↑x : Lˣ) ^ d = 1 := by
      rw [← Subgroup.coe_pow H x d, h1]
      rfl
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have hy_qr : ((↑x : Lˣ) : L) ^ (q ^ r) = ((↑x : Lˣ) : L) := by
    rw [hqr_eq, pow_add, pow_mul, hy_d, one_pow, one_mul, pow_one]
  -- the powers `x ^ 0, …, x ^ r` are pairwise distinct (`r < d`)
  have hinj : ∀ i j : Fin (r + 1), x ^ (i : ℕ) = x ^ (j : ℕ) → i = j := by
    intro i j hij
    have hi : (i : ℕ) < orderOf x := by rw [hx]; omega
    have hj : (j : ℕ) < orderOf x := by rw [hx]; omega
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj hij)
  set S : Finset H := Finset.univ.image (fun i : Fin (r + 1) => x ^ (i : ℕ)) with hS
  have hScard : S.card = r + 1 := by
    have hinj' : Set.InjOn (fun i : Fin (r + 1) => x ^ (i : ℕ))
        ↑(Finset.univ : Finset (Fin (r + 1))) := by
      intro a _ b _ hab; exact hinj a b hab
    rw [hS, Finset.card_image_of_injOn hinj']
    simp
  have hSle : S.card ≤ k := by rw [hScard]; omega
  -- the MDS hypothesis gives linear independence of `1, x, …, x ^ r`
  have hLI : LinearIndependent F (fun (u : S) => ((u.1 : Lˣ) : L)) := h_mds S hSle
  let g : Fin (r + 1) → S :=
    fun i => ⟨x ^ (i : ℕ), by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hinj i j (congrArg Subtype.val hij)
  let v : Fin (r + 1) → L := fun i => ((↑(x ^ (i : ℕ)) : Lˣ) : L)
  have hv : LinearIndependent F v := hLI.comp g hg
  have hLC : Function.Injective (Fintype.linearCombination F v) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  -- the `F`-span of `1, x, …, x ^ r` therefore has `q ^ (r + 1)` elements
  set Z : Finset L := Finset.univ.image (Fintype.linearCombination F v) with hZ
  have hZcard : Z.card = q ^ (r + 1) := by
    have hinjZ : Set.InjOn (Fintype.linearCombination F v)
        ↑(Finset.univ : Finset (Fin (r + 1) → F)) := by
      intro a _ b _ h; exact hLC h
    rw [hZ, Finset.card_image_of_injOn hinjZ, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, hq]
  -- the `r`-th iterate of the Frobenius is `y ↦ y ^ (q ^ r)`
  have hφr : ∀ z : L, (FiniteField.frobeniusAlgHom F L ^ r) z = z ^ (q ^ r) := by
    intro z
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, hq]
  have hv_fix : ∀ i : Fin (r + 1), v i ^ (q ^ r) = v i := by
    intro i
    have hvi : v i = ((↑x : Lˣ) : L) ^ (i : ℕ) := by
      simp [v, Units.val_pow_eq_pow_val]
    rw [hvi, ← pow_mul, Nat.mul_comm (i : ℕ) (q ^ r), pow_mul, hy_qr]
  -- every element of the span is fixed
  have hfix : ∀ c : Fin (r + 1) → F,
      (Fintype.linearCombination F v c) ^ (q ^ r) = Fintype.linearCombination F v c := by
    intro c
    have h1 : (FiniteField.frobeniusAlgHom F L ^ r) (Fintype.linearCombination F v c)
        = Fintype.linearCombination F v c := by
      rw [Fintype.linearCombination_apply, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smulₛₗ, RingHom.id_apply, hφr, hv_fix i]
    rw [← hφr]
    exact h1
  -- hence every element of the span is a root of `X ^ (q ^ r) - X`
  set P : Polynomial L := Polynomial.X ^ (q ^ r) - Polynomial.X with hP
  have hPdeg : P.natDegree = q ^ r := by
    have hlt : (Polynomial.X : Polynomial L).natDegree
        < (Polynomial.X ^ (q ^ r) : Polynomial L).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      have h1 : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr_pos
      have h2 : 2 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq2 r
      omega
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hPdeg
    have h3 : 0 < q ^ r := pow_pos hqpos r
    omega
  have hsub : Z.val ⊆ P.roots := by
    intro z hz
    rw [Polynomial.mem_roots hPne]
    have hz' : z ∈ Z := hz
    rw [hZ] at hz'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz'
    obtain ⟨c, rfl⟩ := hz'
    rw [Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      hfix c, sub_self]
  -- a nonzero polynomial of degree `q ^ r` has at most `q ^ r` roots
  have hbound := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hZcard, hPdeg] at hbound
  have hlt2 : q ^ r < q ^ (r + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega
