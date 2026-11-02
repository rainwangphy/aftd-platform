import AFTD.Prelude
import AFTD.Kb.Tcs.MixedRadixOffset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mixed_radix_offset_bijective

Topic: data_structures   Node: 2f4be7b1f2f7

Provenance: helper lemma. step towards fixed_offset_hash_worst_mean_mixed_radix

For any table size n ≥ 2 and any permutation P of the prime factors of n, the mixed-radix reversed offset sequence mixed_radix_offset n P is a bijection from Fin n to ZMod n.
-/

-- natural-number mixed-radix value (reversed positional weights are `drop`-products)
def mixed_radix_offset_bijective_mdv (L : List ℕ) (j : ℕ) : ℕ :=
  ∑ i : Fin L.length, ((j / (L.take i.val).prod) % L[i.val]) * (L.drop (i.val+1)).prod

-- recursion of the mixed-radix value along the head of the list
lemma mixed_radix_offset_bijective_mdv_cons (p : ℕ) (L : List ℕ) (j : ℕ) :
    mixed_radix_offset_bijective_mdv (p::L) j
      = (j % p) * L.prod + mixed_radix_offset_bijective_mdv L (j / p) := by
  unfold mixed_radix_offset_bijective_mdv
  change (∑ i : Fin (L.length + 1), ((j / (List.take i.val (p :: L)).prod) % (p :: L)[i.val]) * (List.drop (i.val+1) (p :: L)).prod)
    = (j % p) * L.prod + ∑ i : Fin L.length, ((j / p / (L.take i.val).prod) % L[i.val]) * ((L.drop (i.val+1)).prod)
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.take_zero, List.prod_nil, Nat.div_one,
    List.drop_zero, List.drop_succ_cons, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_succ_cons, List.prod_cons, Nat.div_div_eq_div_mul]

-- splitting a natural of the form `a*m + b` with `b < m`
lemma mixed_radix_offset_bijective_mul_add_eq {a c m b d : ℕ} (hm : 0 < m) (hb : b < m) (hd : d < m)
    (h : a*m + b = c*m + d) : a = c ∧ b = d := by
  have ha : (a*m+b)/m = a := by
    rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hc : (c*m+d)/m = c := by
    rw [Nat.mul_comm c m, Nat.mul_add_div hm, Nat.div_eq_of_lt hd, Nat.add_zero]
  have h1 : (a*m+b)/m = (c*m+d)/m := by rw [h]
  rw [ha, hc] at h1
  refine ⟨h1, ?_⟩
  subst h1
  exact Nat.add_left_cancel h

-- the mixed-radix value always lies below the product
lemma mixed_radix_offset_bijective_mdv_lt (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (j : ℕ)
    (hj : j < L.prod) : mixed_radix_offset_bijective_mdv L j < L.prod := by
  induction L generalizing j with
  | nil => simp [mixed_radix_offset_bijective_mdv]
  | cons p L' ih =>
      rw [List.prod_cons] at hj ⊢
      rw [mixed_radix_offset_bijective_mdv_cons]
      have hp : 0 < p := hpos p List.mem_cons_self
      have hpos' : ∀ x ∈ L', 0 < x := fun x hx => hpos x (List.mem_cons_of_mem p hx)
      have hjdiv : j / p < L'.prod := by
        rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm]; exact hj
      have hih := ih hpos' (j / p) hjdiv
      have hmod : j % p < p := Nat.mod_lt j hp
      calc (j % p) * L'.prod + mixed_radix_offset_bijective_mdv L' (j / p)
            < (j % p) * L'.prod + L'.prod := by linarith
        _ = ((j % p) + 1) * L'.prod := by ring
        _ ≤ p * L'.prod := by
              exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hmod)

-- the mixed-radix value is injective on `[0, prod L)`
lemma mixed_radix_offset_bijective_mdv_inj (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) :
    ∀ j1 j2, j1 < L.prod → j2 < L.prod →
      mixed_radix_offset_bijective_mdv L j1 = mixed_radix_offset_bijective_mdv L j2 → j1 = j2 := by
  induction L with
  | nil => intro j1 j2 h1 h2 _; simp at h1 h2; omega
  | cons p L' ih =>
      intro j1 j2 h1 h2 heq
      rw [List.prod_cons] at h1 h2
      rw [mixed_radix_offset_bijective_mdv_cons, mixed_radix_offset_bijective_mdv_cons] at heq
      have hp : 0 < p := hpos p List.mem_cons_self
      have hpos' : ∀ x ∈ L', 0 < x := fun x hx => hpos x (List.mem_cons_of_mem p hx)
      have hm : 0 < L'.prod := List.prod_pos hpos'
      have h1d : j1 / p < L'.prod := by rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm]; exact h1
      have h2d : j2 / p < L'.prod := by rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm]; exact h2
      have hb1 := mixed_radix_offset_bijective_mdv_lt L' hpos' (j1/p) h1d
      have hb2 := mixed_radix_offset_bijective_mdv_lt L' hpos' (j2/p) h2d
      obtain ⟨hmod, hrest⟩ := mixed_radix_offset_bijective_mul_add_eq hm hb1 hb2 heq
      have hdiv : j1 / p = j2 / p := ih hpos' (j1/p) (j2/p) h1d h2d hrest
      have e1 := Nat.div_add_mod j1 p
      have e2 := Nat.div_add_mod j2 p
      rw [hdiv, hmod] at e1
      omega

lemma mixed_radix_offset_bijective_nat_div_of_mul_eq {A D n : ℕ} (hA : 0 < A) (h : A * D = n) :
    n / A = D := by
  rw [← h, Nat.mul_div_right D hA]

lemma mixed_radix_offset_bijective_prod_take_pos (L : List ℕ) (h : 0 < L.prod) (k : ℕ) :
    0 < (L.take k).prod := by
  rcases Nat.eq_zero_or_pos (L.take k).prod with h0 | h0
  · exfalso
    have hp := List.prod_take_mul_prod_drop L k
    rw [h0, Nat.zero_mul] at hp
    omega
  · exact h0

-- the original `ZMod` offset is the natural mixed-radix value, reduced mod `n`
lemma mixed_radix_offset_bijective_eq_mdv (n : ℕ) (L : List ℕ) (hprod : L.prod = n)
    (hL0 : 0 < L.prod) (j : Fin n) :
    mixed_radix_offset n L j = (mixed_radix_offset_bijective_mdv L j.val : ZMod n) := by
  simp only [mixed_radix_offset, mixed_radix_offset_bijective_mdv, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [mixed_radix_offset_bijective_nat_div_of_mul_eq
    (mixed_radix_offset_bijective_prod_take_pos L hL0 (i.val+1))
    (by rw [List.prod_take_mul_prod_drop, hprod])]

/-- The mixed-radix reversed offset sequence mixed_radix_offset n P is a bijection from Fin n to ZMod n for any permutation P of the prime factors of n. -/
theorem mixed_radix_offset_bijective
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (P : List ℕ) (hP : P.Perm (Nat.primeFactorsList n)) :
    Function.Bijective (mixed_radix_offset n P) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hprod : P.prod = n := hP.prod_eq.trans (Nat.prod_primeFactorsList hn0)
  have hL0 : 0 < P.prod := by rw [hprod]; omega
  have hpos : ∀ x ∈ P, 0 < x := by
    intro x hx
    exact Nat.Prime.pos (Nat.prime_of_mem_primeFactorsList ((hP.mem_iff).mp hx))
  have hinj : Function.Injective (mixed_radix_offset n P) := by
    intro j1 j2 heq
    rw [mixed_radix_offset_bijective_eq_mdv n P hprod hL0 j1,
        mixed_radix_offset_bijective_eq_mdv n P hprod hL0 j2] at heq
    have h1 : j1.val < P.prod := by rw [hprod]; exact j1.isLt
    have h2 : j2.val < P.prod := by rw [hprod]; exact j2.isLt
    have b1 : mixed_radix_offset_bijective_mdv P j1.val < n :=
      lt_of_lt_of_eq (mixed_radix_offset_bijective_mdv_lt P hpos j1.val h1) hprod
    have b2 : mixed_radix_offset_bijective_mdv P j2.val < n :=
      lt_of_lt_of_eq (mixed_radix_offset_bijective_mdv_lt P hpos j2.val h2) hprod
    have heq' : mixed_radix_offset_bijective_mdv P j1.val
        = mixed_radix_offset_bijective_mdv P j2.val := by
      have hmod := (ZMod.natCast_eq_natCast_iff
        (mixed_radix_offset_bijective_mdv P j1.val)
        (mixed_radix_offset_bijective_mdv P j2.val) n).mp heq
      exact Nat.ModEq.eq_of_lt_of_lt hmod b1 b2
    exact Fin.ext (mixed_radix_offset_bijective_mdv_inj P hpos _ _ h1 h2 heq')
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, ZMod.card]⟩
