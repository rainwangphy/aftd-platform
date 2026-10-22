import AFTD.Prelude
import AFTD.Kb.Tcs.IsTraceMdsSubgroup
import AFTD.Kb.Tcs.SubgroupUnitsPowCardDvd

/-!
# subgroup_rigidity_order_of_mds

Topic: information   Node: 32395e0c717a

Provenance: formalization of a published result. Source: arXiv:2610.28047 Theorem 3.1

Let H be a cyclic subgroup of order n in the multiplicative group of a degree-k field extension L of F_q with 2 <= k <= n - 2. If every subset of H of size at most k is linearly independent over F_q, then for every divisor d > 1 of n, the multiplicative order of q modulo d equals k.
-/

open IntermediateField in
/-- If a finite-field element `x` satisfies `x ^ (#F ^ r) = x`, then the degree of its
minimal polynomial over `F` divides `r`. -/
lemma subgroup_rigidity_order_of_mds_finrank_adjoin_dvd
    {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] [Finite L]
    {r : ℕ} {x : L} (hx : x ^ (Fintype.card F ^ r) = x) :
    Module.finrank F (IntermediateField.adjoin F {x}) ∣ r := by
  let K : IntermediateField F L := IntermediateField.adjoin F {x}
  haveI : Finite K := inferInstance
  have hord : orderOf (FiniteField.frobeniusAlgHom F K) = Module.finrank F K :=
    FiniteField.orderOf_frobeniusAlgHom F K
  rw [← hord]
  refine orderOf_dvd_iff_pow_eq_one.mpr ?_
  refine IntermediateField.adjoin_algHom_ext F (s := {x}) ?_
  intro y hy
  obtain rfl : y = x := by simpa using hy
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply]
  exact Subtype.ext (by simpa using hx)

/-- Subgroup rigidity: any cyclic subgroup of order n with the MDS property forces the order of q mod d to be k for every divisor d > 1 of n. -/
theorem subgroup_rigidity_order_of_mds {F L : Type*} [Field F] [Fintype F] [Field L] [Algebra F L] (q n k : ℕ) (H : Subgroup Lˣ) [Fintype H] (hH_cyc : IsCyclic H) (hH_card : Fintype.card H = n) (hq : Fintype.card F = q) (hdim : Module.finrank F L = k) (hk : 2 ≤ k) (hkn : k ≤ n - 2) (h_mds : is_trace_mds_subgroup F H k) : ∀ d : ℕ, d ∣ n → 1 < d → orderOf (q : ZMod d) = k := by
  classical
  intro d hdn hd1
  haveI : Module.Finite F L := Module.finite_of_finrank_pos (by rw [hdim]; omega)
  haveI : Finite L := Module.finite_of_finite F
  haveI : Fintype L := Fintype.ofFinite L
  have hnk : 4 ≤ n := by omega
  have hq2 : 2 ≤ q := by rw [← hq]; exact Fintype.one_lt_card
  have hcardL : Fintype.card L = q ^ k := by
    rw [Module.card_eq_pow_finrank (K := F) (V := L), hq, hdim]
  have key : d ∣ q ^ k - 1 := by
    have h1 : Fintype.card H ∣ Fintype.card Lˣ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card H
    rw [hH_card, Fintype.card_units, hcardL] at h1
    exact dvd_trans hdn h1
  haveI : NeZero d := ⟨by omega⟩
  have hqk : (q : ZMod d) ^ k = 1 := by
    have hzero : ((q ^ k - 1 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr key
    have hone : 1 ≤ q ^ k := Nat.one_le_pow k q (by omega)
    calc (q : ZMod d) ^ k = ((q ^ k : ℕ) : ZMod d) := by push_cast; ring
      _ = ((q ^ k - 1 + 1 : ℕ) : ZMod d) := by rw [Nat.sub_add_cancel hone]
      _ = ((q ^ k - 1 : ℕ) : ZMod d) + 1 := by push_cast; ring
      _ = 1 := by rw [hzero, zero_add]
  have hr_dvd_k : orderOf (q : ZMod d) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hqk
  have hrle : orderOf (q : ZMod d) ≤ k := Nat.le_of_dvd (by omega) hr_dvd_k
  have hrpos : 0 < orderOf (q : ZMod d) := Nat.pos_of_dvd_of_pos hr_dvd_k (by omega)
  have hr_lt_d : orderOf (q : ZMod d) < d := by
    have hunit : IsUnit (q : ZMod d) := (isUnit_pow_iff (by omega : k ≠ 0)).mp (hqk ▸ isUnit_one)
    have hcop : q.Coprime d := (ZMod.isUnit_iff_coprime q d).mp hunit
    have hdiv : orderOf (q : ZMod d) ∣ Nat.totient d := by
      rw [← ZMod.coe_unitOfCoprime q hcop, orderOf_units, ← ZMod.card_units_eq_totient]
      exact orderOf_dvd_card
    have htpos : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    have hle : orderOf (q : ZMod d) ≤ d - 1 := by
      have h1 := Nat.le_of_dvd htpos hdiv
      have h2 := Nat.totient_lt d hd1
      omega
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have hgn : orderOf g = n := by rw [hg, Nat.card_eq_fintype_card, hH_card]
  set x : H := g ^ (n / d) with hx_def
  have hx_ord : orderOf x = d := by
    rw [hx_def, ← hgn]
    exact orderOf_pow_orderOf_div (by omega) (by rw [hgn]; exact hdn)
  have hxL_ord : orderOf ((x : Lˣ)) = d := by
    rw [Subgroup.orderOf_coe, hx_ord]
  have hx_d : ((x : Lˣ) : L) ^ d = 1 := by
    have h := pow_orderOf_eq_one (x : Lˣ)
    rw [hxL_ord] at h
    simpa using congrArg (fun u : Lˣ => (u : L)) h
  have hdvd_r : d ∣ q ^ orderOf (q : ZMod d) - 1 := by
    have hrpow : (q : ZMod d) ^ orderOf (q : ZMod d) = 1 := pow_orderOf_eq_one _
    have h : q ^ orderOf (q : ZMod d) ≡ 1 [MOD d] :=
      (ZMod.natCast_eq_natCast_iff (q ^ orderOf (q : ZMod d)) 1 d).mp (by simpa using hrpow)
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ q (by omega))).mp h.symm
  have hxL_pow : ((x : Lˣ) : L) ^ (q ^ orderOf (q : ZMod d)) = ((x : Lˣ) : L) := by
    obtain ⟨t, ht⟩ := hdvd_r
    have h1 : ((x : Lˣ) : L) ^ (q ^ orderOf (q : ZMod d) - 1) = 1 := by
      rw [ht, pow_mul, hx_d, one_pow]
    rw [← Nat.sub_add_cancel (Nat.one_le_pow _ q (by omega)), pow_add, h1, one_mul, pow_one]
  set K : IntermediateField F L := IntermediateField.adjoin F {((x : Lˣ) : L)} with hK
  set m : ℕ := Module.finrank F K with hm
  have hmdvd : m ∣ orderOf (q : ZMod d) := by
    have := subgroup_rigidity_order_of_mds_finrank_adjoin_dvd (F := F) (L := L)
      (r := orderOf (q : ZMod d)) (x := ((x : Lˣ) : L)) (by rw [hq]; exact hxL_pow)
    simpa [hm, hK] using this
  have hmle : m ≤ orderOf (q : ZMod d) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · omega
    · exact Nat.le_of_dvd hrpos hmdvd
  have hkm : k ≤ m := by
    by_contra hcon
    push Not at hcon
    have hmd' : m ≤ d - 1 := by omega
    let φ : ℕ → H := fun j => ⟨((x : Lˣ)) ^ j, H.pow_mem x.2 j⟩
    have hφinj : Set.InjOn φ ↑(Finset.range (m + 1)) := by
      intro j hj j' hj' heq
      rw [Finset.mem_coe, Finset.mem_range] at hj hj'
      have heq2 : ((x : Lˣ)) ^ j = ((x : Lˣ)) ^ j' := by
        have h2 := congrArg (fun u : H => ((u : Lˣ))) heq
        simpa [φ] using h2
      have hmod : j ≡ j' [MOD d] := by
        have h3 := pow_eq_pow_iff_modEq.mp heq2
        rwa [hxL_ord] at h3
      exact hmod.eq_of_lt_of_lt (by omega) (by omega)
    set S : Finset H := (Finset.range (m + 1)).image φ with hS
    have hScard : S.card = m + 1 := by
      rw [hS, Finset.card_image_of_injOn hφinj, Finset.card_range]
    have hSk : S.card ≤ k := by omega
    have hind := h_mds S hSk
    have hmem : ∀ u : S, ((u.1 : Lˣ) : L) ∈ K := by
      intro u
      obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp u.2
      have hu : u.1 = φ j := hju.symm
      rw [hu]
      have hxK : ((x : Lˣ) : L) ∈ K :=
        IntermediateField.subset_adjoin F {((x : Lˣ) : L)} (Set.mem_singleton _)
      have hp : ((φ j : H) : Lˣ) = ((x : Lˣ)) ^ j := rfl
      rw [hp]
      push_cast
      exact pow_mem hxK j
    have hindK : LinearIndependent F (fun u : S => (⟨((u.1 : Lˣ) : L), hmem u⟩ : ↥K.toSubmodule)) :=
      LinearIndependent.of_comp (Submodule.subtype K.toSubmodule) hind
    have hfin : Fintype.card S ≤ Module.finrank F ↥K.toSubmodule := hindK.fintype_card_le_finrank
    rw [Fintype.card_coe, hScard] at hfin
    have hfm : Module.finrank F ↥K.toSubmodule = m := rfl
    omega
  omega
