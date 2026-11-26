import AFTD.Prelude
import AFTD.Kb.Tcs.ConnectedIntersectionDensity
import AFTD.Kb.Tcs.ConnectionDensityLeConnectedIntersectionDensity
import AFTD.Kb.Tcs.ExistsGeneratingConnectionSetConnectedIntersectionDensity
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.ConnectionDensity
import AFTD.Kb.Tcs.IsGeneratingConnectionSet
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# connected_intersection_density_elementary_abelian_square_times_cyclic

Topic: combinatorics   Node: c75ce6d0a6df

Provenance: original. Related work: arXiv:2611.26732, Section 7 open problem (closed formula for ρ_gen((C_{p^u} × C_{p^v}) × C_{q^a})); the paper proves ρ_gen(C_p^r) = p^{1-r} (Prop. 1.5) and the lower bound (m-1)/(m-1+|T|) of Corollary 2.11, and lists C_6 × C_2 = 3/4 in Table 1

Let $p \ne q$ be primes and $a \ge 1$, $m = q^a$, and $G = (C_p \times C_p) \times C_{q^a}$ (as `Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))`). Then $\rho_{\mathrm{gen}}(G) = \frac{(m-1)p + k}{p(m-1+k)}$ where $k = 2$ if $p = 2$ and $k = 4$ if $p$ is odd. So $\rho_{\mathrm{gen}} = m/(m+1)$ for $p=2$ and $((m-1)p+4)/(p(m+3))$ for odd $p$. This is the case $u = v = 1$ of the open problem.
-/

theorem op2165_mem_zpowers_iff {A : Type*} [AddGroup A] (g h : Multiplicative A) :
    g ∈ Subgroup.zpowers h ↔
      Multiplicative.toAdd g ∈ AddSubgroup.zmultiples (Multiplicative.toAdd h) := by
  rw [Subgroup.mem_zpowers_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [toAdd_zpow]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by apply Multiplicative.toAdd.injective; simp [toAdd_zpow, hk]⟩

theorem op2165_crt (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (j k : ℤ) :
    ∃ n : ℤ, (n : ZMod p) = j ∧ (n : ZMod (q ^ a)) = k := by
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  refine ⟨k + (j - k) * ((q : ℤ) ^ a) ^ (p - 1), ?_, ?_⟩
  · have hq0 : (q : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    have h1 : ((q : ZMod p) ^ a) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one (pow_ne_zero _ hq0)
    push_cast
    rw [h1]; ring
  · have h0 : ((q : ZMod (q ^ a)) ^ a) = 0 := by exact_mod_cast ZMod.natCast_self (q ^ a)
    have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    push_cast
    rw [h0, zero_pow hp1]; ring

theorem op2165_prod_mem (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {y y' : ZMod p × ZMod p} {w w' : ZMod (q ^ a)}
    (hy : y ∈ AddSubgroup.zmultiples y') (hw : w ∈ AddSubgroup.zmultiples w') :
    ((y, w) : (ZMod p × ZMod p) × ZMod (q ^ a)) ∈ AddSubgroup.zmultiples (y', w') := by
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  obtain ⟨n, hn1, hn2⟩ := op2165_crt p q a hpq j k
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
  rw [Prod.smul_mk]
  congr 1
  · rw [← Int.cast_smul_eq_zsmul (ZMod p), hn1, Int.cast_smul_eq_zsmul]
  · rw [← Int.cast_smul_eq_zsmul (ZMod (q ^ a)), hn2, Int.cast_smul_eq_zsmul]

theorem op2165_fst_mem {B C : Type*} [AddGroup B] [AddGroup C] {y y' : B} {w w' : C}
    (h : ((y, w) : B × C) ∈ AddSubgroup.zmultiples (y', w')) : y ∈ AddSubgroup.zmultiples y' := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Prod.fst hk⟩

theorem op2165_zmod_gcd (n x : ℕ) :
    AddSubgroup.zmultiples ((x : ZMod n)) = AddSubgroup.zmultiples (((x.gcd n : ℕ)) : ZMod n) := by
  apply le_antisymm
  · rw [AddSubgroup.zmultiples_le]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((x / x.gcd n : ℕ) : ℤ), ?_⟩
    rw [natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left x n)]
  · rw [AddSubgroup.zmultiples_le]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨x.gcdA n, ?_⟩
    rw [zsmul_eq_mul]
    have := Nat.gcd_eq_gcd_ab x n
    have h2 : ((x.gcd n : ℕ) : ZMod n) = (((x.gcd n : ℕ) : ℤ) : ZMod n) := by simp
    rw [h2, this]; push_cast; rw [ZMod.natCast_self]; ring

theorem op2165_zmod_prime_pow_total (q a : ℕ) [Fact q.Prime] (w w' : ZMod (q ^ a)) :
    w ∈ AddSubgroup.zmultiples w' ∨ w' ∈ AddSubgroup.zmultiples w := by
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have key : ∀ v : ZMod (q ^ a), ∃ i : ℕ,
      AddSubgroup.zmultiples v = AddSubgroup.zmultiples ((q ^ i : ℕ) : ZMod (q ^ a)) := by
    intro v
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).mp (Nat.gcd_dvd_right v.val (q ^ a))
    refine ⟨i, ?_⟩
    rw [← hi, ← op2165_zmod_gcd, ZMod.natCast_zmod_val]
  have mono : ∀ i j : ℕ, i ≤ j → AddSubgroup.zmultiples ((q ^ j : ℕ) : ZMod (q ^ a)) ≤
      AddSubgroup.zmultiples ((q ^ i : ℕ) : ZMod (q ^ a)) := by
    intro i j hij
    rw [AddSubgroup.zmultiples_le]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((q ^ (j - i) : ℕ) : ℤ), ?_⟩
    rw [natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hij]
  obtain ⟨i, hi⟩ := key w
  obtain ⟨j, hj⟩ := key w'
  rcases le_total i j with h | h
  · right
    have : w' ∈ AddSubgroup.zmultiples w' := AddSubgroup.mem_zmultiples w'
    rw [hj] at this; rw [hi]; exact mono i j h this
  · left
    have : w ∈ AddSubgroup.zmultiples w := AddSubgroup.mem_zmultiples w
    rw [hi] at this; rw [hj]; exact mono j i h this

theorem op2165_p_nsmul (p : ℕ) [Fact p.Prime] (u : ZMod p × ZMod p) : p • u = 0 := by
  ext <;> simp [nsmul_eq_mul]

theorem op2165_line (p : ℕ) [Fact p.Prime] {u v : ZMod p × ZMod p} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u ∈ AddSubgroup.zmultiples v) : AddSubgroup.zmultiples u = AddSubgroup.zmultiples v := by
  have hle : AddSubgroup.zmultiples u ≤ AddSubgroup.zmultiples v := AddSubgroup.zmultiples_le.mpr h
  apply AddSubgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zmultiples, Nat.card_zmultiples, addOrderOf_eq_prime (op2165_p_nsmul p u) hu,
    addOrderOf_eq_prime (op2165_p_nsmul p v) hv]

theorem op2165_adj_imp (p : ℕ) [Fact p.Prime] {x y : ZMod p × ZMod p} (hx : x ≠ 0)
    (h : y ∈ AddSubgroup.zmultiples (x + y) ∨ x + y ∈ AddSubgroup.zmultiples y) :
    y ∈ AddSubgroup.zmultiples x := by
  by_cases hy : y = 0
  · rw [hy]; exact zero_mem _
  rcases h with h | h
  · have hxy : x + y ≠ 0 := by
      intro h0; rw [h0, AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.mem_bot] at h; exact hy h
    have e1 := op2165_line p hy hxy h
    have hx' : x ∈ AddSubgroup.zmultiples y := by
      rw [e1]
      simpa using sub_mem (AddSubgroup.mem_zmultiples (x + y)) h
    rw [op2165_line p hx hy hx']; exact AddSubgroup.mem_zmultiples y
  · by_cases hxy : x + y = 0
    · have : y = -x := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hxy
      rw [this]; exact neg_mem (AddSubgroup.mem_zmultiples x)
    have e1 := op2165_line p hxy hy h
    have hx' : x ∈ AddSubgroup.zmultiples y := by
      simpa using sub_mem h (AddSubgroup.mem_zmultiples y)
    rw [op2165_line p hx hy hx']; exact AddSubgroup.mem_zmultiples y

theorem op2165_imp_adj (p : ℕ) [Fact p.Prime] {x y : ZMod p × ZMod p} (hx : x ≠ 0)
    (h : y ∈ AddSubgroup.zmultiples x) :
    y ∈ AddSubgroup.zmultiples (x + y) ∨ x + y ∈ AddSubgroup.zmultiples y := by
  by_cases hxy : x + y = 0
  · right; rw [hxy]; exact zero_mem _
  left
  have hm : x + y ∈ AddSubgroup.zmultiples x := add_mem (AddSubgroup.mem_zmultiples x) h
  rw [op2165_line p hxy hx hm]; exact h

theorem op2165_card_fiber {B C : Type*} [AddGroup B] [AddGroup C] (H : AddSubgroup B) :
    Nat.card {g : Multiplicative (B × C) | (Multiplicative.toAdd g).1 ∈ H} =
      Nat.card H * Nat.card C := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact { toFun := fun g => (⟨(Multiplicative.toAdd g.1).1, g.2⟩, (Multiplicative.toAdd g.1).2)
          invFun := fun hc => ⟨Multiplicative.ofAdd (hc.1.1, hc.2), by simpa using hc.1.2⟩
          left_inv := fun g => Subtype.ext (by simp)
          right_inv := fun _ => rfl }

theorem op2165_c_le (p q a : ℕ) [Fact p.Prime] [Fact q.Prime]
    (x : ZMod p × ZMod p) (hx : x ≠ 0) (z : ZMod (q ^ a)) :
    c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) (Multiplicative.ofAdd (x, z)) ≤ p * q ^ a := by
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  unfold c
  calc _ ≤ Nat.card {g : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)) |
          (Multiplicative.toAdd g).1 ∈ AddSubgroup.zmultiples x} := by
        apply Nat.card_mono (Set.toFinite _)
        intro g hg
        simp only [Set.mem_setOf_eq, op2165_mem_zpowers_iff, toAdd_mul, toAdd_ofAdd] at hg ⊢
        generalize Multiplicative.toAdd g = t at hg ⊢
        obtain ⟨y, w⟩ := t
        simp only [Prod.mk_add_mk] at hg ⊢
        apply op2165_adj_imp p hx
        rcases hg with hg | hg
        · left
          exact op2165_fst_mem hg
        · right
          exact op2165_fst_mem hg
    _ = p * q ^ a := by
        rw [op2165_card_fiber, Nat.card_zmultiples, addOrderOf_eq_prime (op2165_p_nsmul p x) hx,
          Nat.card_zmod]

theorem op2165_c_ge (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (x : ZMod p × ZMod p) (hx : x ≠ 0) :
    p * q ^ a ≤ c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) (Multiplicative.ofAdd (x, 0)) := by
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  unfold c
  calc p * q ^ a = Nat.card {g : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)) |
          (Multiplicative.toAdd g).1 ∈ AddSubgroup.zmultiples x} := by
        rw [op2165_card_fiber, Nat.card_zmultiples, addOrderOf_eq_prime (op2165_p_nsmul p x) hx,
          Nat.card_zmod]
    _ ≤ _ := by
        apply Nat.card_mono (Set.toFinite _)
        intro g hg
        simp only [Set.mem_setOf_eq, op2165_mem_zpowers_iff, toAdd_mul, toAdd_ofAdd] at hg ⊢
        generalize Multiplicative.toAdd g = t at hg ⊢
        obtain ⟨y, w⟩ := t
        simp only [Prod.mk_add_mk, zero_add] at hg ⊢
        rcases op2165_imp_adj p hx hg with h | h
        · left
          exact op2165_prod_mem p q a hpq h (by simp)
        · right
          exact op2165_prod_mem p q a hpq h (by simp)

theorem op2165_c_eq (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (z : ZMod (q ^ a)) :
    c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) (Multiplicative.ofAdd (0, z)) =
      p * p * q ^ a := by
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  unfold c
  have : {g : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)) |
      g ∈ Subgroup.zpowers (Multiplicative.ofAdd (0, z) * g) ∨
        Multiplicative.ofAdd (0, z) * g ∈ Subgroup.zpowers g} = Set.univ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, op2165_mem_zpowers_iff, toAdd_mul,
      toAdd_ofAdd]
    generalize Multiplicative.toAdd g = t
    obtain ⟨y, w⟩ := t
    simp only [Prod.mk_add_mk, zero_add]
    rcases op2165_zmod_prime_pow_total q a w (z + w) with h | h
    · left
      exact op2165_prod_mem p q a hpq (AddSubgroup.mem_zmultiples y) h
    · right
      exact op2165_prod_mem p q a hpq (AddSubgroup.mem_zmultiples y) h
  rw [this, Nat.card_univ, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, ZMod.card]

theorem op2165_card_G (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Fintype.card (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) = p * p * q ^ a := by
  simp [Fintype.card_prod, ZMod.card]

theorem op2165_c_le_card (G : Type*) [Group G] [Fintype G] (s : G) : c G s ≤ Fintype.card G := by
  unfold c
  calc _ ≤ Nat.card (Set.univ : Set G) := Nat.card_mono Set.finite_univ (Set.subset_univ _)
    _ = _ := by rw [Nat.card_univ, Nat.card_eq_fintype_card]

theorem op2165_not_all_in_line (p q a : ℕ) [Fact p.Prime] [Fact q.Prime]
    (S : Finset (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))))
    (hgen : Subgroup.closure (S : Set (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)))) = ⊤)
    (x₀ : ZMod p × ZMod p) :
    ∃ s ∈ S, (Multiplicative.toAdd s).1 ∉ AddSubgroup.zmultiples x₀ := by
  by_contra hcon
  push_neg at hcon
  have hp := (Fact.out : p.Prime)
  let K : Subgroup (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) :=
    { carrier := {g | (Multiplicative.toAdd g).1 ∈ AddSubgroup.zmultiples x₀}
      mul_mem' := fun {g h} hg hh => by
        simp only [Set.mem_setOf_eq, toAdd_mul, Prod.fst_add] at hg hh ⊢
        exact add_mem hg hh
      one_mem' := by simp
      inv_mem' := fun {g} hg => by
        simp only [Set.mem_setOf_eq, toAdd_inv, Prod.fst_neg] at hg ⊢
        exact neg_mem hg }
  have hle : Subgroup.closure (S : Set _) ≤ K := (Subgroup.closure_le K).mpr (fun s hs => hcon s hs)
  rw [hgen] at hle
  have hall : ∀ y : ZMod p × ZMod p, y ∈ AddSubgroup.zmultiples x₀ := by
    intro y
    have := hle (Subgroup.mem_top (Multiplicative.ofAdd ((y, 0) : (ZMod p × ZMod p) × ZMod (q ^ a))))
    simpa [K] using this
  have htop : AddSubgroup.zmultiples x₀ = ⊤ := eq_top_iff.mpr (fun y _ => hall y)
  have hc1 : Nat.card (AddSubgroup.zmultiples x₀) ≤ p := by
    rw [Nat.card_zmultiples]
    exact addOrderOf_le_of_nsmul_eq_zero hp.pos (op2165_p_nsmul p x₀)
  rw [htop, AddSubgroup.card_top, Nat.card_prod, Nat.card_zmod] at hc1
  nlinarith [hp.two_le]

theorem op2165_ne_neg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {x : ZMod p × ZMod p} (hx : x ≠ 0) :
    -x ≠ x := by
  intro h
  apply hx
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  have h1 := congrArg Prod.fst h
  have h2' := congrArg Prod.snd h
  simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2'
  ext
  · have : (2 : ZMod p) * x.1 = 0 := by linear_combination -h1
    simpa [h2] using this
  · have : (2 : ZMod p) * x.2 = 0 := by linear_combination -h2'
    simpa [h2] using this

theorem op2165_alg_upper (P M K a r T : ℚ) (hP : 2 ≤ P) (hM : 2 ≤ M) (hK : 0 < K) (ha : 0 ≤ a)
    (haM : a ≤ M - 1) (hr : K ≤ r) (hT : T ≤ a * (P * P * M) + r * (P * M)) :
    T / ((P * P * M) * (a + r)) ≤ ((M - 1) * P + K) / (P * ((M - 1) + K)) := by
  have hPM : 0 < P * P * M := by
    have := mul_pos (mul_pos (by linarith : (0:ℚ) < P) (by linarith : (0:ℚ) < P)) (by linarith : (0:ℚ) < M)
    exact this
  have h1 : 0 < (P * P * M) * (a + r) := mul_pos hPM (by linarith)
  have h2 : 0 < P * ((M - 1) + K) := mul_pos (by linarith) (by linarith)
  rw [div_le_div_iff₀ h1 h2]
  have k1 : 0 ≤ (r - K) * (M - 1) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ K * (M - 1 - a) := mul_nonneg hK.le (by linarith)
  have key : 0 ≤ (P - 1) * (r * (M - 1) - a * K) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right hT h2.le, mul_nonneg hPM.le key]

theorem op2165_alg_lower (P M K r T : ℚ) (hP : 2 ≤ P) (hM : 2 ≤ M) (hr0 : 0 ≤ r) (hrK : r ≤ K)
    (hT : (M - 1) * (P * P * M) + r * (P * M) ≤ T) :
    ((M - 1) * P + K) / (P * ((M - 1) + K)) ≤ T / ((P * P * M) * ((M - 1) + r)) := by
  have hPM : 0 < P * P * M := by
    have := mul_pos (mul_pos (by linarith : (0:ℚ) < P) (by linarith : (0:ℚ) < P)) (by linarith : (0:ℚ) < M)
    exact this
  have h1 : 0 < (P * P * M) * ((M - 1) + r) := mul_pos hPM (by linarith)
  have h2 : 0 < P * ((M - 1) + K) := mul_pos (by linarith) (by linarith)
  rw [div_le_div_iff₀ h2 h1]
  have key : 0 ≤ (M - 1) * (P - 1) * (K - r) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hT h2.le, mul_nonneg hPM.le key]

theorem op2165_upper (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (ha : 1 ≤ a)
    (S : Finset (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))))
    (hS : is_generating_connection_set (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) S) :
    connection_density (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) S ≤
      (((q : ℚ) ^ a - 1) * p + (if p = 2 then 2 else 4)) /
        ((p : ℚ) * (((q : ℚ) ^ a - 1) + (if p = 2 then 2 else 4))) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  obtain ⟨h1S, hinv, hgen⟩ := hS
  obtain ⟨s₁, hs₁, hs₁n⟩ := op2165_not_all_in_line p q a S hgen 0
  obtain ⟨s₂, hs₂, hs₂n⟩ := op2165_not_all_in_line p q a S hgen (Multiplicative.toAdd s₁).1
  have hx1 : (Multiplicative.toAdd s₁).1 ≠ 0 := by
    intro h; apply hs₁n; rw [h]; exact zero_mem _
  have hx2 : (Multiplicative.toAdd s₂).1 ≠ 0 := by
    intro h; apply hs₂n; rw [h]; exact zero_mem _
  have hRmem : ∀ s ∈ S, (Multiplicative.toAdd s).1 ≠ 0 →
      s ∈ S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0) := fun s hs h =>
    Finset.mem_filter.mpr ⟨hs, h⟩
  have hinvfst : ∀ s : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)),
      (Multiplicative.toAdd s⁻¹).1 = -(Multiplicative.toAdd s).1 := fun s => by simp [toAdd_inv]
  have hRk : (if p = 2 then 2 else 4) ≤ (S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0)).card := by
    have h12 : s₁ ≠ s₂ := by rintro rfl; exact hs₂n (AddSubgroup.mem_zmultiples _)
    split_ifs with hp2
    · calc 2 = ({s₁, s₂} : Finset _).card := (Finset.card_pair h12).symm
        _ ≤ _ := Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hRmem _ hs₁ hx1
          · exact hRmem _ hs₂ hx2)
    · have d1 : s₁ ≠ s₁⁻¹ := fun h => op2165_ne_neg p hp2 hx1 (by
        have := congrArg (fun g => (Multiplicative.toAdd g).1) h
        simp only [hinvfst] at this; exact this.symm)
      have d2 : s₂ ≠ s₂⁻¹ := fun h => op2165_ne_neg p hp2 hx2 (by
        have := congrArg (fun g => (Multiplicative.toAdd g).1) h
        simp only [hinvfst] at this; exact this.symm)
      have h12' : s₁ ≠ s₂⁻¹ := by
        intro h; apply hs₂n
        have : s₂ = s₁⁻¹ := by rw [h, inv_inv]
        rw [this, hinvfst]; exact neg_mem (AddSubgroup.mem_zmultiples _)
      have h1'2 : s₁⁻¹ ≠ s₂ := by
        intro h; apply hs₂n
        rw [← h, hinvfst]; exact neg_mem (AddSubgroup.mem_zmultiples _)
      have h1'2' : s₁⁻¹ ≠ s₂⁻¹ := fun h => h12 (inv_injective h)
      have hc4 : ({s₁, s₁⁻¹, s₂, s₂⁻¹} : Finset _).card = 4 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d1, h12, h12'⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1'2, h1'2'⟩),
          Finset.card_pair d2]
      rw [← hc4]
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hRmem _ hs₁ hx1
      · exact hRmem _ (hinv _ hs₁) (by rw [hinvfst]; exact neg_ne_zero.mpr hx1)
      · exact hRmem _ hs₂ hx2
      · exact hRmem _ (hinv _ hs₂) (by rw [hinvfst]; exact neg_ne_zero.mpr hx2)
  have hAcard : (S.filter (fun g => (Multiplicative.toAdd g).1 = 0)).card ≤ q ^ a - 1 := by
    have := Finset.card_le_card_of_injOn
      (fun g : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)) => (Multiplicative.toAdd g).2)
      (s := S.filter (fun g => (Multiplicative.toAdd g).1 = 0)) (t := (Finset.univ : Finset (ZMod (q ^ a))).erase 0) (by
        intro g hg
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hg
        rw [Finset.mem_coe, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h0
        apply h1S
        have : g = 1 := by
          apply Multiplicative.toAdd.injective
          simp only [toAdd_one]
          exact Prod.ext hg.2 h0
        rw [← this]; exact hg.1) (by
        intro g hg g' hg' e
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hg hg'
        apply Multiplicative.toAdd.injective
        exact Prod.ext (hg.2.trans hg'.2.symm) e)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at this
  have hsplit := (Finset.sum_filter_add_sum_filter_not S (fun g => (Multiplicative.toAdd g).1 = 0)
    (fun s => (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ))).symm
  have hcard := Finset.card_filter_add_card_filter_not
    (s := S) (fun g => (Multiplicative.toAdd g).1 = 0)
  have hsA : ∑ s ∈ S.filter (fun g => (Multiplicative.toAdd g).1 = 0),
      (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ) ≤
      ((S.filter (fun g => (Multiplicative.toAdd g).1 = 0)).card : ℚ) * ((p : ℚ) * p * (q : ℚ) ^ a) := by
    have := Finset.sum_le_card_nsmul (S.filter (fun g => (Multiplicative.toAdd g).1 = 0))
      (fun s => (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ)) ((p : ℚ) * p * (q : ℚ) ^ a)
      (fun s _ => by
        have := op2165_c_le_card (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s
        rw [op2165_card_G] at this
        exact_mod_cast this)
    simpa [nsmul_eq_mul] using this
  have hsR : ∑ s ∈ S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0),
      (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ) ≤
      ((S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0)).card : ℚ) * ((p : ℚ) * (q : ℚ) ^ a) := by
    have := Finset.sum_le_card_nsmul (S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0))
      (fun s => (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ)) ((p : ℚ) * (q : ℚ) ^ a)
      (fun s hs => by
        have hne := (Finset.mem_filter.mp hs).2
        have := op2165_c_le p q a (Multiplicative.toAdd s).1 hne (Multiplicative.toAdd s).2
        simp only [Prod.mk.eta, ofAdd_toAdd] at this
        exact_mod_cast this)
    simpa [nsmul_eq_mul] using this
  unfold connection_density
  rw [op2165_card_G, ← hcard, hsplit]
  have hM : (2 : ℚ) ≤ (q : ℚ) ^ a := by
    have : 2 ≤ q ^ a := le_trans hq.two_le (Nat.le_self_pow (by omega) q)
    exact_mod_cast this
  have hAcard' : ((S.filter (fun g => (Multiplicative.toAdd g).1 = 0)).card : ℚ) ≤ (q : ℚ) ^ a - 1 := by
    have h1 : 1 ≤ q ^ a := Nat.one_le_pow _ _ hq.pos
    have := (Nat.cast_le (α := ℚ)).mpr hAcard
    rw [Nat.cast_sub h1] at this
    simpa using this
  have hRk' : ((if p = 2 then 2 else 4 : ℕ) : ℚ) ≤
      ((S.filter (fun g => ¬ (Multiplicative.toAdd g).1 = 0)).card : ℚ) := by exact_mod_cast hRk
  have hKeq : ((if p = 2 then 2 else 4 : ℕ) : ℚ) = (if p = 2 then 2 else 4 : ℚ) := by
    split_ifs <;> norm_num
  rw [hKeq] at hRk'
  push_cast
  apply op2165_alg_upper (p : ℚ) ((q : ℚ) ^ a) (if p = 2 then 2 else 4) _ _ _
    (by exact_mod_cast hp.two_le) hM (by split_ifs <;> norm_num) (by positivity) hAcard' hRk'
  linarith [hsA, hsR]

theorem op2165_lower (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (ha : 1 ≤ a) :
    ∃ S : Finset (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))),
      is_generating_connection_set (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) S ∧
      (((q : ℚ) ^ a - 1) * p + (if p = 2 then 2 else 4)) /
        ((p : ℚ) * (((q : ℚ) ^ a - 1) + (if p = 2 then 2 else 4))) ≤
      connection_density (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) S := by
  classical
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  have : NeZero (q ^ a) := ⟨pow_ne_zero _ hq.ne_zero⟩
  let e1 : ZMod p × ZMod p := (1, 0)
  let e2 : ZMod p × ZMod p := (0, 1)
  have he1 : e1 ≠ 0 := by
    intro h; have := congrArg Prod.fst h; simp [e1] at this
  have he2 : e2 ≠ 0 := by
    intro h; have := congrArg Prod.snd h; simp [e2] at this
  let X : Finset (ZMod p × ZMod p) := {e1, -e1, e2, -e2}
  have hX0 : ∀ x ∈ X, x ≠ 0 := by
    intro x hx
    simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact he1
    · exact neg_ne_zero.mpr he1
    · exact he2
    · exact neg_ne_zero.mpr he2
  have hXneg : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  have hXcard : X.card ≤ (if p = 2 then 2 else 4) := by
    split_ifs with hp2
    · have hneg : ∀ x : ZMod p × ZMod p, -x = x := by
        intro x; subst hp2
        exact Prod.ext (ZMod.neg_eq_self_mod_two _) (ZMod.neg_eq_self_mod_two _)
      calc X.card ≤ ({e1, e2} : Finset _).card := Finset.card_le_card (by
            intro x hx
            simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl | rfl | rfl <;> simp [hneg])
        _ ≤ 2 := Finset.card_le_two
    · exact Finset.card_le_four
  let A0 : Finset (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) :=
    (Finset.univ.filter (fun g => (Multiplicative.toAdd g).1 = 0)).erase 1
  let R0 : Finset (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) :=
    X.image (fun x => Multiplicative.ofAdd (x, 0))
  have hfilter : (Finset.univ.filter
      (fun g : Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)) => (Multiplicative.toAdd g).1 = 0)) =
      (Finset.univ : Finset (ZMod (q ^ a))).image
        (fun z => Multiplicative.ofAdd ((0 : ZMod p × ZMod p), z)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨(Multiplicative.toAdd g).2, Multiplicative.toAdd.injective (by simp [Prod.ext_iff, h])⟩
    · rintro ⟨z, rfl⟩
      simp
  have hA0card : A0.card = q ^ a - 1 := by
    simp only [A0]
    rw [Finset.card_erase_of_mem (by simp), hfilter, Finset.card_image_of_injective _ (by
      intro z z' h
      simpa using congrArg (fun g => (Multiplicative.toAdd g).2) h), Finset.card_univ, ZMod.card]
  have hR0card : R0.card ≤ (if p = 2 then 2 else 4) := (Finset.card_image_le).trans hXcard
  have hdisj : Disjoint A0 R0 := by
    rw [Finset.disjoint_left]
    intro g hgA hgR
    simp only [A0, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hgA
    simp only [R0, Finset.mem_image] at hgR
    obtain ⟨x, hx, rfl⟩ := hgR
    simp only [toAdd_ofAdd] at hgA
    exact hX0 x hx hgA.2
  refine ⟨A0 ∪ R0, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- 1 ∉ S
    rw [Finset.mem_union, not_or]
    refine ⟨Finset.notMem_erase _ _, ?_⟩
    simp only [R0, Finset.mem_image, not_exists, not_and]
    intro x hx h
    apply hX0 x hx
    have := congrArg (fun g => (Multiplicative.toAdd g).1) h
    simpa using this
  · -- inverse closed
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · simp only [A0, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      apply Finset.mem_union_left
      simp only [A0, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨inv_ne_one.mpr hs.1, by simp [toAdd_inv, hs.2]⟩
    · simp only [R0, Finset.mem_image] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      apply Finset.mem_union_right
      simp only [R0, Finset.mem_image]
      exact ⟨-x, hXneg x hx, Multiplicative.toAdd.injective (by simp [toAdd_inv])⟩
  · -- generates
    rw [eq_top_iff]
    intro g _
    have hdecomp : g = Multiplicative.ofAdd ((0 : ZMod p × ZMod p), (Multiplicative.toAdd g).2) *
        (Multiplicative.ofAdd (e1, (0 : ZMod (q ^ a)))) ^ ((Multiplicative.toAdd g).1.1.val) *
        (Multiplicative.ofAdd (e2, (0 : ZMod (q ^ a)))) ^ ((Multiplicative.toAdd g).1.2.val) := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd]
      ext <;> simp [e1, e2, nsmul_eq_mul]
    rw [hdecomp]
    refine mul_mem (mul_mem ?_ (pow_mem (Subgroup.subset_closure ?_) _))
      (pow_mem (Subgroup.subset_closure ?_) _)
    · by_cases hw : (Multiplicative.toAdd g).2 = 0
      · rw [hw]; simp only [Prod.mk_zero_zero, ofAdd_zero]; exact one_mem _
      · apply Subgroup.subset_closure
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, A0, Finset.mem_erase,
          Finset.mem_filter, Finset.mem_univ, true_and, toAdd_ofAdd]
        left
        refine ⟨?_, by simp⟩
        intro h
        apply hw
        have := congrArg (fun g => (Multiplicative.toAdd g).2) h
        simpa using this
    · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, R0, Finset.mem_image]
      right; exact ⟨e1, by simp [X], rfl⟩
    · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, R0, Finset.mem_image]
      right; exact ⟨e2, by simp [X], rfl⟩
  · -- density
    unfold connection_density
    rw [Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj, op2165_card_G, hA0card]
    have hsA : ∑ s ∈ A0, (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ) =
        (A0.card : ℚ) * ((p : ℚ) * p * (q : ℚ) ^ a) := by
      rw [Finset.sum_congr rfl (g := fun _ => ((p : ℚ) * p * (q : ℚ) ^ a)), Finset.sum_const,
        nsmul_eq_mul]
      intro s hs
      simp only [A0, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have h := op2165_c_eq p q a hpq (Multiplicative.toAdd s).2
      have hs' : Multiplicative.ofAdd ((0 : ZMod p × ZMod p), (Multiplicative.toAdd s).2) = s := by
        apply Multiplicative.toAdd.injective
        simp [Prod.ext_iff, hs.2]
      rw [hs'] at h
      rw [h]; push_cast; ring
    have hsR : (R0.card : ℚ) * ((p : ℚ) * (q : ℚ) ^ a) ≤
        ∑ s ∈ R0, (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ) := by
      have := Finset.card_nsmul_le_sum R0
        (fun s => (c (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) s : ℚ))
        ((p : ℚ) * (q : ℚ) ^ a) (fun s hs => by
          simp only [R0, Finset.mem_image] at hs
          obtain ⟨x, hx, rfl⟩ := hs
          exact_mod_cast op2165_c_ge p q a hpq x (hX0 x hx))
      simpa [nsmul_eq_mul] using this
    rw [hsA, hA0card]
    have h1 : 1 ≤ q ^ a := Nat.one_le_pow _ _ hq.pos
    have hM : (2 : ℚ) ≤ (q : ℚ) ^ a := by
      have : 2 ≤ q ^ a := le_trans hq.two_le (Nat.le_self_pow (by omega) q)
      exact_mod_cast this
    have hRk' : (R0.card : ℚ) ≤ (if p = 2 then 2 else 4 : ℚ) := by
      have : (R0.card : ℚ) ≤ ((if p = 2 then 2 else 4 : ℕ) : ℚ) := by exact_mod_cast hR0card
      refine this.trans (le_of_eq ?_)
      split_ifs <;> norm_num
    push_cast [Nat.cast_sub h1]
    apply op2165_alg_lower (p : ℚ) ((q : ℚ) ^ a) _ (R0.card : ℚ) _ (by exact_mod_cast hp.two_le) hM
      (by positivity) hRk'
    linarith [hsR]

theorem connected_intersection_density_elementary_abelian_square_times_cyclic (p q a : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (ha : 1 ≤ a) : connected_intersection_density (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a))) = (((q : ℚ) ^ a - 1) * p + (if p = 2 then 2 else 4)) / ((p : ℚ) * (((q : ℚ) ^ a - 1) + (if p = 2 then 2 else 4))) := by
  apply le_antisymm
  · obtain ⟨S, hS, hEq⟩ := exists_generating_connection_set_connected_intersection_density
      (Multiplicative ((ZMod p × ZMod p) × ZMod (q ^ a)))
    rw [← hEq]
    exact op2165_upper p q a hpq ha S hS
  · obtain ⟨S, hS, hle⟩ := op2165_lower p q a hpq ha
    exact hle.trans (connection_density_le_connected_intersection_density _ S hS)
