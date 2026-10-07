import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome
import AFTD.Kb.Tcs.Gf8MultCoeff
import AFTD.Kb.Tcs.Gf8OracleSyndromeSingleton

/-!
# gf8_oracle_t_count_ge_20

Topic: quantum   Node: bd2bebe89c62

Provenance: formalization of a published result. Source: arXiv:2610.01024, Proposition 59 (slice-rank floor), special case k = 3

The slice-rank floor of arXiv:2610.01024 Proposition 59 at k = 3: every parity representation of the GF(8) multiplication oracle's syndrome has at least G(3) = 20 parities (every nonzero slice of the multiplication tensor has rank 6, so the column code is an even self-orthogonal [t, 9, 8] code, and the Griesmer bound gives t >= 20).
-/

/-- One ordered term of the GF(8) oracle syndrome on triples: `T(q, r, l)` when the three
qubits lie in registers x, y, z in this order. -/
def gf8_syn_ord (a b c : Fin 9) : ZMod 2 :=
  if a.val / 3 = 0 ∧ b.val / 3 = 1 ∧ c.val / 3 = 2 then
    gf8_mult_coeff ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨b.val % 3, Nat.mod_lt _ (by norm_num)⟩
      ⟨c.val % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- The GF(8) oracle syndrome on triples, symmetrized over the six orders. -/
def gf8_syn_sym (i j k : Fin 9) : ZMod 2 :=
  gf8_syn_ord i j k + gf8_syn_ord i k j + gf8_syn_ord j i k + gf8_syn_ord j k i +
    gf8_syn_ord k i j + gf8_syn_ord k j i

theorem gf8_syndrome_pair (i j : Fin 9) : gf8_oracle_syndrome {i, j} = 0 := by
  revert i j; decide

theorem gf8_syndrome_triple (i j k : Fin 9) : gf8_oracle_syndrome {i, j, k} = gf8_syn_sym i j k := by
  revert i j k; decide


theorem gf8_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Qubit `t` of register `b` (x = 0, y = 1, z = 2). -/
def gf8_row (b t : Fin 3) : Fin 9 := ⟨3 * b.val + t.val, by omega⟩

/-- The first register other than `β`. -/
def gf8_other1 (β : Fin 3) : Fin 3 := ![1, 0, 0] β

/-- The second register other than `β`. -/
def gf8_other2 (β : Fin 3) : Fin 3 := ![2, 2, 1] β

/-- The 3 × 3 block of a slice of the GF(8) syndrome tensor, contracted with `c` on register `β`,
between the two other registers. -/
def gf8_amat (β : Fin 3) (c : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun q r => ∑ t, c t * gf8_syn_sym (gf8_row β t) (gf8_row (gf8_other1 β) q)
    (gf8_row (gf8_other2 β) r)

theorem gf8_syn_sym_off (β : Fin 3) (i : Fin 9) (q r : Fin 3) (hi : i.val / 3 ≠ β.val) :
    gf8_syn_sym i (gf8_row (gf8_other1 β) q) (gf8_row (gf8_other2 β) r) = 0 := by
  revert β i q r; decide

theorem gf8_syn_sym_same (i j k : Fin 9) (h : j.val / 3 = k.val / 3) : gf8_syn_sym i j k = 0 := by
  revert i j k; decide

theorem gf8_syn_sym_swap (i j k : Fin 9) : gf8_syn_sym i j k = gf8_syn_sym i k j := by
  unfold gf8_syn_sym; ring

theorem gf8_amat_det (β : Fin 3) (c : Fin 3 → ZMod 2) (hc : c ≠ 0) : (gf8_amat β c).det ≠ 0 := by
  have key : ∀ (β : Fin 3) (c0 c1 c2 : ZMod 2), ¬(c0 = 0 ∧ c1 = 0 ∧ c2 = 0) →
      gf8_amat β ![c0, c1, c2] 0 0 * gf8_amat β ![c0, c1, c2] 1 1 * gf8_amat β ![c0, c1, c2] 2 2 -
        gf8_amat β ![c0, c1, c2] 0 0 * gf8_amat β ![c0, c1, c2] 1 2 * gf8_amat β ![c0, c1, c2] 2 1 -
        gf8_amat β ![c0, c1, c2] 0 1 * gf8_amat β ![c0, c1, c2] 1 0 * gf8_amat β ![c0, c1, c2] 2 2 +
        gf8_amat β ![c0, c1, c2] 0 1 * gf8_amat β ![c0, c1, c2] 1 2 * gf8_amat β ![c0, c1, c2] 2 0 +
        gf8_amat β ![c0, c1, c2] 0 2 * gf8_amat β ![c0, c1, c2] 1 0 * gf8_amat β ![c0, c1, c2] 2 1 -
        gf8_amat β ![c0, c1, c2] 0 2 * gf8_amat β ![c0, c1, c2] 1 1 * gf8_amat β ![c0, c1, c2] 2 0 ≠ 0 := by
    decide
  have hc' : c = ![c 0, c 1, c 2] := by ext t; fin_cases t <;> rfl
  rw [Matrix.det_fin_three, hc']
  apply key
  rintro ⟨h0, h1, h2⟩
  apply hc
  rw [hc']
  ext t
  fin_cases t <;> simp [h0, h1, h2]

theorem gf8_block_sum (β : Fin 3) (lam : Fin 9 → ZMod 2) (q r : Fin 3) :
    ∑ i, lam i * gf8_syn_sym i (gf8_row (gf8_other1 β) q) (gf8_row (gf8_other2 β) r) =
      gf8_amat β (fun t => lam (gf8_row β t)) q r := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin 3)), ∀ y ∈ (Finset.univ : Finset (Fin 3)),
      gf8_row β x = gf8_row β y → x = y := by
    intro x _ y _ h
    simp only [gf8_row, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  simp only [gf8_amat, Matrix.of_apply]
  rw [← Finset.sum_image (f := fun i => lam i * gf8_syn_sym i (gf8_row (gf8_other1 β) q)
    (gf8_row (gf8_other2 β) r)) hinj]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hne : i.val / 3 ≠ β.val := by
    intro h
    apply hi
    refine Finset.mem_image.2 ⟨⟨i.val % 3, by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    simp only [gf8_row]
    omega
  rw [gf8_syn_sym_off β i q r hne, mul_zero]

/-- Counting the parities of a representation that a functional `lam` sees as odd, weighted by
`A ⊆ y`, gives a contraction of the syndrome. -/
theorem gf8_W_sum (S : Finset (Finset (Fin 9))) (hS : is_parity_repr S gf8_oracle_syndrome)
    (lam : Fin 9 → ZMod 2) (A : Finset (Fin 9)) (hA : A.card ≤ 2) :
    ∑ y ∈ S.filter (fun y => ∑ i ∈ y, lam i = 1), (if A ⊆ y then (1 : ZMod 2) else 0) =
      ∑ i, lam i * gf8_oracle_syndrome (insert i A) := by
  classical
  rw [Finset.sum_filter]
  have h1 : ∀ y : Finset (Fin 9),
      (if ∑ i ∈ y, lam i = 1 then (if A ⊆ y then (1 : ZMod 2) else 0) else 0) =
        ∑ i, lam i * (if insert i A ⊆ y then 1 else 0) := by
    intro y
    have h2 : ∑ i, lam i * (if insert i A ⊆ y then (1 : ZMod 2) else 0) =
        (∑ i ∈ y, lam i) * (if A ⊆ y then 1 else 0) := by
      rw [Finset.sum_mul]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ y)
      · intro i hi
        have : i ∉ y := (Finset.mem_sdiff.1 hi).2
        simp [Finset.insert_subset_iff, this]
      · intro i hi
        simp [Finset.insert_subset_iff, hi]
    rw [h2]
    rcases gf8_zmod2_cases (∑ i ∈ y, lam i) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  congr 1
  apply hS.2
  exact ⟨Finset.card_pos.2 (Finset.insert_nonempty _ _),
    (Finset.card_insert_le _ _).trans (by omega)⟩

open Matrix in
theorem gf8_weight_ge_seven (S : Finset (Finset (Fin 9))) (hS : is_parity_repr S gf8_oracle_syndrome)
    (lam : Fin 9 → ZMod 2) (hlam : lam ≠ 0) :
    7 ≤ (S.filter fun y => ∑ i ∈ y, lam i = 1).card := by
  classical
  set W := S.filter fun y => ∑ i ∈ y, lam i = 1 with hW
  have hsum := gf8_W_sum S hS lam
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hlam
  let β : Fin 3 := ⟨i0.val / 3, by omega⟩
  let c : Fin 3 → ZMod 2 := fun t => lam (gf8_row β t)
  have hc : c ≠ 0 := by
    intro h
    apply hi0
    have h' : gf8_row β ⟨i0.val % 3, by omega⟩ = i0 := by
      ext
      simp only [gf8_row, β]
      omega
    rw [← h']
    exact congrFun h _
  let rowof : Fin 3 ⊕ Fin 3 → Fin 9 := Sum.elim (gf8_row (gf8_other1 β)) (gf8_row (gf8_other2 β))
  let Z : Matrix (Fin 3 ⊕ Fin 3) W (ZMod 2) := fun a y => if rowof a ∈ y.1 then 1 else 0
  let A := gf8_amat β c
  have hentry : ∀ a b, (Z * Zᵀ) a b = ∑ i, lam i * gf8_syn_sym i (rowof a) (rowof b) := by
    intro a b
    rw [Matrix.mul_apply]
    have : ∀ y : W, Z a y * Zᵀ y b =
        if ({rowof a, rowof b} : Finset (Fin 9)) ⊆ y.1 then 1 else 0 := by
      intro y
      show (if rowof a ∈ y.1 then (1 : ZMod 2) else 0) * (if rowof b ∈ y.1 then 1 else 0) = _
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun y _ => this y]
    rw [Finset.sum_coe_sort W
      (fun y => if ({rowof a, rowof b} : Finset (Fin 9)) ⊆ y then (1 : ZMod 2) else 0)]
    rw [hsum _ Finset.card_le_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gf8_syndrome_triple]
  have hblk1 : ∀ q, (rowof (Sum.inl q)).val / 3 = (gf8_other1 β).val := by
    intro q; simp only [rowof, Sum.elim_inl, gf8_row]; omega
  have hblk2 : ∀ q, (rowof (Sum.inr q)).val / 3 = (gf8_other2 β).val := by
    intro q; simp only [rowof, Sum.elim_inr, gf8_row]; omega
  have hZZ : Z * Zᵀ = Matrix.fromBlocks 0 A Aᵀ 0 := by
    ext a b
    rw [hentry]
    rcases a with q | q <;> rcases b with r | r
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [gf8_syn_sym_same _ _ _ (by rw [hblk1, hblk1]), mul_zero]
    · rw [Matrix.fromBlocks_apply₁₂]
      exact gf8_block_sum β lam q r
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      show _ = gf8_amat β c r q
      rw [← gf8_block_sum β lam r q]
      exact Finset.sum_congr rfl fun i _ => by rw [gf8_syn_sym_swap]; rfl
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [gf8_syn_sym_same _ _ _ (by rw [hblk2, hblk2]), mul_zero]
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (gf8_amat_det β c hc)
  have hmul : Matrix.fromBlocks 0 A Aᵀ 0 * Matrix.fromBlocks 0 A⁻¹ᵀ A⁻¹ 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_nonsing_inv _ hA,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.transpose_one]
  have hN : 6 ≤ (Matrix.fromBlocks 0 A Aᵀ 0).rank := by
    have := Matrix.rank_mul_le_left (Matrix.fromBlocks 0 A Aᵀ 0) (Matrix.fromBlocks 0 A⁻¹ᵀ A⁻¹ 0)
    rw [hmul, Matrix.rank_one] at this
    simpa using this
  have hcol : Z *ᵥ (fun _ => 1) = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, Z]
    rw [Finset.sum_coe_sort W (fun y => if rowof a ∈ y then (1 : ZMod 2) else 0)]
    have := hsum {rowof a} (by simp)
    simp only [Finset.singleton_subset_iff] at this
    rw [this]
    exact Finset.sum_eq_zero fun i _ => by rw [gf8_syndrome_pair, mul_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker Z.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  have hker : 0 < W.card → 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker Z.mulVecLin) := by
    intro hpos
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : (fun _ => (1 : ZMod 2)) ∈ LinearMap.ker Z.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hcol]
    rw [h0, Submodule.mem_bot] at hmem
    obtain ⟨y, hy⟩ := Finset.card_pos.1 hpos
    have := congrFun hmem ⟨y, hy⟩
    simp at this
  have hle : (Z * Zᵀ).rank ≤ Z.rank := Matrix.rank_mul_le_left _ _
  rw [hZZ] at hle
  unfold Matrix.rank at hle
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · have : Module.finrank (ZMod 2) (LinearMap.range Z.mulVecLin) ≤ 0 := by omega
    unfold Matrix.rank at hN
    omega
  · have := hker hpos
    unfold Matrix.rank at hN
    omega

theorem gf8_weight_ge_eight (S : Finset (Finset (Fin 9))) (hS : is_parity_repr S gf8_oracle_syndrome)
    (lam : Fin 9 → ZMod 2) (hlam : lam ≠ 0) :
    8 ≤ (S.filter fun y => ∑ i ∈ y, lam i = 1).card := by
  classical
  have h7 := gf8_weight_ge_seven S hS lam hlam
  have heven : ((S.filter fun y => ∑ i ∈ y, lam i = 1).card : ZMod 2) = 0 := by
    have := gf8_W_sum S hS lam ∅ (by simp)
    simp only [Finset.empty_subset, ite_true, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    rw [this]
    exact Finset.sum_eq_zero fun i _ => by
      rw [Finset.insert_empty, gf8_oracle_syndrome_singleton, mul_zero]
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff_even).1 heven
  omega


/-- The length bound `∑_{i<k} ⌈d / 2^i⌉` for binary linear codes, written recursively. -/
def binary_code_len_bound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, d => d + binary_code_len_bound k ((d + 1) / 2)

/-- Length bound for binary linear codes (by residual codes), in the language of point sets: if every nonzero linear functional on a
`k`-dimensional `𝔽₂`-space takes the value `1` on at least `d` points of `P`, then
`P` has at least `∑_{i<k} ⌈d / 2^i⌉` points. -/
theorem binary_points_len_bound : ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V], Module.finrank (ZMod 2) V = k →
    ∀ (P : Finset V) (d : ℕ),
      (∀ φ : Module.Dual (ZMod 2) V, φ ≠ 0 → d ≤ (P.filter fun y => φ y = 1).card) →
      binary_code_len_bound k d ≤ P.card := by
  intro k
  induction k with
  | zero => intros; simp [binary_code_len_bound]
  | succ k ih =>
    intro V _ _ _ hk P d hP
    classical
    have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have hex : ∃ m, ∃ φ : Module.Dual (ZMod 2) V, φ ≠ 0 ∧
        (P.filter fun y => φ y = 1).card = m := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) V, φ v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) v).1 h)
      exact ⟨_, φ, fun h => hφ (by simp [h]), rfl⟩
    obtain ⟨φ0, hφ0, hw0⟩ := Nat.find_spec hex
    have hmin : ∀ φ : Module.Dual (ZMod 2) V, φ ≠ 0 →
        Nat.find hex ≤ (P.filter fun y => φ y = 1).card :=
      fun φ hφ => Nat.find_min' hex ⟨φ, hφ, rfl⟩
    have hdw : d ≤ Nat.find hex := hw0 ▸ hP φ0 hφ0
    obtain ⟨v0, hv0⟩ : ∃ v, φ0 v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ0 (LinearMap.ext h)
    have hv01 : φ0 v0 = 1 := (gf8_zmod2_cases _).resolve_left hv0
    let H := LinearMap.ker φ0
    have hH : Module.finrank (ZMod 2) H = k := by
      have h1 := LinearMap.finrank_range_add_finrank_ker φ0
      have h2 : LinearMap.range φ0 = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro b
        rcases gf8_zmod2_cases b with rfl | rfl
        · exact ⟨0, map_zero _⟩
        · exact ⟨v0, hv01⟩
      rw [h2, finrank_top, Module.finrank_self] at h1
      show Module.finrank (ZMod 2) (LinearMap.ker φ0) = k
      omega
    let P' : Finset H := P.subtype (· ∈ H)
    have hcount : ∀ (p q : V → Prop) [DecidablePred p] [DecidablePred q],
        (∀ y, (if p y then 1 else 0) + (if q y then 1 else 0) = 1) →
        (P.filter p).card + (P.filter q).card = P.card := by
      intro p q _ _ h
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun y _ => h y
    have hP' : P'.card = (P.filter fun y => φ0 y = 0).card := by
      rw [Finset.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr fun y _ => LinearMap.mem_ker)
    have hsplit : (P.filter fun y => φ0 y = 0).card + (P.filter fun y => φ0 y = 1).card =
        P.card := by
      apply hcount
      intro y
      rcases gf8_zmod2_cases (φ0 y) with h | h <;> simp [h]
    have hrec : ∀ ψ : Module.Dual (ZMod 2) H, ψ ≠ 0 →
        (d + 1) / 2 ≤ (P'.filter fun y => ψ y = 1).card := by
      intro ψ hψ
      obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ψ
      have hφH : ∀ y : H, φ y = ψ y := fun y => by
        rw [← hφ]
        rfl
      have hne1 : φ ≠ 0 := by
        rintro rfl
        apply hψ
        ext y
        rw [← hφH]
        rfl
      have hne2 : φ + φ0 ≠ 0 := by
        intro h0
        apply hψ
        ext y
        have : (φ + φ0) y = 0 := by rw [h0]; rfl
        rw [LinearMap.add_apply, LinearMap.mem_ker.1 y.2, add_zero] at this
        rw [← hφH, this]
        rfl
      have c1 := hmin φ hne1
      have c2 := hmin (φ + φ0) hne2
      have hmap : (P'.filter fun y => ψ y = 1).map (Function.Embedding.subtype _) =
          P.filter fun y => φ0 y = 0 ∧ φ y = 1 := by
        ext y
        constructor
        · intro hy
          obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
          rw [Finset.mem_filter, Finset.mem_subtype] at hy'
          refine Finset.mem_filter.2 ⟨hy'.1, LinearMap.mem_ker.1 y'.2, ?_⟩
          show φ (y' : V) = 1
          rw [hφH]
          exact hy'.2
        · intro hy
          rw [Finset.mem_filter] at hy
          refine Finset.mem_map.2 ⟨⟨y, LinearMap.mem_ker.2 hy.2.1⟩,
            Finset.mem_filter.2 ⟨Finset.mem_subtype.2 hy.1, ?_⟩, rfl⟩
          rw [← hφH]
          exact hy.2.2
      have hr : (P'.filter fun y => ψ y = 1).card =
          (P.filter fun y => φ0 y = 0 ∧ φ y = 1).card := by
        rw [← hmap, Finset.card_map]
      have hsum : (P.filter fun y => φ y = 1).card + (P.filter fun y => (φ + φ0) y = 1).card =
          2 * (P.filter fun y => φ0 y = 0 ∧ φ y = 1).card +
            (P.filter fun y => φ0 y = 1).card := by
        simp only [Finset.card_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [LinearMap.add_apply]
        rcases gf8_zmod2_cases (φ y) with h1 | h1 <;> rcases gf8_zmod2_cases (φ0 y) with h2 | h2 <;>
          simp [h1, h2]
      rw [hr]
      omega
    have := ih H hH P' ((d + 1) / 2) hrec
    show d + binary_code_len_bound k ((d + 1) / 2) ≤ P.card
    omega

theorem gf8_oracle_t_count_ge_20 (S : Finset (Finset (Fin 9))) (hS : is_parity_repr S gf8_oracle_syndrome) : 20 ≤ S.card := by
  classical
  let ind : Finset (Fin 9) → (Fin 9 → ZMod 2) := fun y i => if i ∈ y then 1 else 0
  have hinj : Function.Injective ind := by
    intro y y' h
    ext i
    have := congrFun h i
    simp only [ind] at this
    by_cases h1 : i ∈ y <;> by_cases h2 : i ∈ y' <;> simp_all
  have hG := binary_points_len_bound 9 (Fin 9 → ZMod 2) (Module.finrank_fin_fun (ZMod 2))
    (S.image ind) 8 ?_
  · rw [Finset.card_image_of_injective _ hinj] at hG
    have h20 : binary_code_len_bound 9 8 = 20 := by decide
    omega
  · intro φ hφ
    let lam : Fin 9 → ZMod 2 := fun i => φ (fun j => if i = j then 1 else 0)
    have hφv : ∀ x, φ x = ∑ i, x i * lam i := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ]
      rfl
    have hlam : lam ≠ 0 := by
      intro h
      apply hφ
      refine LinearMap.ext fun x => ?_
      rw [hφv]
      simp [h]
    have hind : ∀ y, φ (ind y) = ∑ i ∈ y, lam i := by
      intro y
      rw [hφv]
      simp only [ind, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
    simp only [hind]
    exact gf8_weight_ge_eight S hS lam hlam
