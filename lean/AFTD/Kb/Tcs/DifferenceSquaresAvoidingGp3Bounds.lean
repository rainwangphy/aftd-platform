import AFTD.Prelude
import AFTD.Kb.Tcs.HasNondegenerateGp3
import AFTD.Kb.Tcs.DiffSquares
import AFTD.Kb.Tcs.TwoPowFourNeOneOfPrimeGeSeven
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# difference_squares_avoiding_gp3_bounds

Topic: combinatorics   Node: 95e039b19e88

Provenance: formalization of a published result. Source: arXiv:2610.34758 Lemma 3.1

Let $p \ge 7$ be a prime and let $A \subset \mathbb{F}_p$ be nonempty. If the set of squared differences $(A - A)^2$ contains no nondegenerate three-term geometric progression, then $|A|^3 \le p^2$, $|A - A| \ge |A|^{5/4}$, and for every $t \in \mathbb{F}_p^\times$ with $t^4 \neq 1$ and every $s \in \mathbb{F}_p$, $|\{(a, b) \in A^2 : b - t a = s\}| \le p / |A|$.
-/

lemma difference_squares_avoiding_gp3_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h1
  omega

lemma difference_squares_avoiding_gp3_phi_inj {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)}
    (hGP : ¬ has_nondegenerate_gp3 (diff_squares A : Set (ZMod p)))
    {t : ZMod p} (ht0 : t ≠ 0) (ht4 : t ^ 4 ≠ 1)
    {a b c a' b' c' : ZMod p}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (ha' : a' ∈ A) (hb' : b' ∈ A) (hc' : c' ∈ A)
    (h1 : b - t * a = b' - t * a') (h2 : c - t * b = c' - t * b') :
    a = a' ∧ b = b' ∧ c = c' := by
  have hbb : b - b' = t * (a - a') := by linear_combination h1
  have hcc : c - c' = t ^ 2 * (a - a') := by
    calc c - c' = t * (b - b') := by linear_combination h2
    _ = t * (t * (a - a')) := by rw [hbb]
    _ = t ^ 2 * (a - a') := by ring
  by_cases haa : a = a'
  · subst haa
    have hb_eq : b = b' := by
      have : b - b' = 0 := by rw [hbb, sub_self, mul_zero]
      exact sub_eq_zero.mp this
    subst hb_eq
    have hc_eq : c = c' := by
      have : c - c' = 0 := by rw [hcc, sub_self, mul_zero]
      exact sub_eq_zero.mp this
    exact ⟨rfl, rfl, hc_eq⟩
  · exfalso
    apply hGP
    refine ⟨(a - a') ^ 2, t ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h0
      have : a - a' = 0 := sq_eq_zero_iff.mp h0
      exact haa (sub_eq_zero.mp this)
    · intro ht2
      apply ht0
      exact sq_eq_zero_iff.mp ht2
    · intro hr2
      apply ht4
      calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = 1 := hr2
    · rw [diff_squares, Finset.mem_coe, Finset.mem_image]
      exact ⟨(a, a'), Finset.mem_product.mpr ⟨ha, ha'⟩, rfl⟩
    · rw [diff_squares, Finset.mem_coe, Finset.mem_image]
      refine ⟨(b, b'), Finset.mem_product.mpr ⟨hb, hb'⟩, ?_⟩
      dsimp
      rw [hbb]
      ring
    · rw [diff_squares, Finset.mem_coe, Finset.mem_image]
      refine ⟨(c, c'), Finset.mem_product.mpr ⟨hc, hc'⟩, ?_⟩
      dsimp
      rw [hcc]
      ring

open scoped Pointwise in
lemma difference_squares_avoiding_gp3_pluennecke_petridis {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A : Finset G} (hA : A.Nonempty) : ∃ X : Finset G, X.Nonempty ∧ X ⊆ A ∧
    (X - A - A).card * A.card ^ 2 ≤ (A - A).card ^ 2 * X.card := by
  have hA' : A ∈ A.powerset.erase ∅ := Finset.mem_erase_of_ne_of_mem hA.ne_empty (Finset.mem_powerset_self _)
  obtain ⟨X, hXmem, hXmin⟩ :=
    Finset.exists_min_image (A.powerset.erase ∅) (fun C ↦ ((C + (-A)).card : ℚ≥0) / C.card) ⟨A, hA'⟩
  rw [Finset.mem_erase, Finset.mem_powerset, ← Finset.nonempty_iff_ne_empty] at hXmem
  obtain ⟨hXnonempty, hXA⟩ := hXmem
  refine ⟨X, hXnonempty, hXA, ?_⟩
  have hXratio : ∀ X' ⊆ X, (X + -A).card * X'.card ≤ (X' + -A).card * X.card := by
    intro X' hX'X
    by_cases hX'empty : X' = ∅
    · rw [hX'empty, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
    · have hX'mem : X' ∈ A.powerset.erase ∅ := by
        rw [Finset.mem_erase, Finset.mem_powerset]
        exact ⟨hX'empty, hX'X.trans hXA⟩
      have hle := hXmin X' hX'mem
      have hX_pos : (0 : ℚ≥0) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hXnonempty)
      have hX'_pos : (0 : ℚ≥0) < X'.card := Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hX'empty))
      rw [div_le_div_iff₀ hX_pos hX'_pos] at hle
      exact_mod_cast hle
  have h_pp := Finset.pluennecke_petridis_inequality_add (-A) hXratio
  have h_min_A := hXmin A hA'
  have hX_pos : (0 : ℚ≥0) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hXnonempty)
  have hA_pos : (0 : ℚ≥0) < A.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  rw [div_le_div_iff₀ hX_pos hA_pos] at h_min_A
  have h_bound : (X + -A).card * A.card ≤ (A + -A).card * X.card := by exact_mod_cast h_min_A
  have h_rew : -A + X + -A = X - A - A := by
    rw [add_comm (-A) X, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have h_rew2 : -A + X = X - A := by
    rw [add_comm, ← sub_eq_add_neg]
  have h_rew3 : X + -A = X - A := by
    rw [← sub_eq_add_neg]
  have h_rew4 : A + -A = A - A := by
    rw [← sub_eq_add_neg]
  rw [h_rew, h_rew2, h_rew3] at h_pp
  rw [h_rew3, h_rew4] at h_bound
  have hXcard_pos : 0 < X.card := Finset.card_pos.mpr hXnonempty
  have h1 : (X - A - A).card * X.card * A.card ^ 2 ≤ (X - A).card ^ 2 * A.card ^ 2 := by
    calc (X - A - A).card * X.card * A.card ^ 2
      _ = ((X - A - A).card * X.card) * A.card ^ 2 := by ring
      _ ≤ ((X - A).card * (X - A).card) * A.card ^ 2 := by gcongr
      _ = (X - A).card ^ 2 * A.card ^ 2 := by ring
  have h2 : (X - A).card ^ 2 * A.card ^ 2 = ((X - A).card * A.card) ^ 2 := by ring
  have h3 : ((X - A).card * A.card) ^ 2 ≤ ((A - A).card * X.card) ^ 2 := by
    exact Nat.pow_le_pow_left h_bound 2
  have h4 : ((A - A).card * X.card) ^ 2 = (A - A).card ^ 2 * X.card * X.card := by ring
  have h5 : (X - A - A).card * A.card ^ 2 * X.card ≤ (A - A).card ^ 2 * X.card * X.card := by
    calc (X - A - A).card * A.card ^ 2 * X.card
      _ = (X - A - A).card * X.card * A.card ^ 2 := by ring
      _ ≤ (X - A).card ^ 2 * A.card ^ 2 := h1
      _ = ((X - A).card * A.card) ^ 2 := h2
      _ ≤ ((A - A).card * X.card) ^ 2 := h3
      _ = (A - A).card ^ 2 * X.card * X.card := h4
  exact Nat.le_of_mul_le_mul_right h5 hXcard_pos

lemma difference_squares_avoiding_gp3_real_pow {a b : ℕ} (h : a ^ 5 ≤ b ^ 4) :
    (a : ℝ) ^ (5 / 4 : ℝ) ≤ (b : ℝ) := by
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  by_cases ha0 : a = 0
  · subst ha0
    simp
  have h_cast : (a : ℝ) ^ 5 ≤ (b : ℝ) ^ 4 := by exact_mod_cast h
  have h_cast' : (a : ℝ) ^ ((5 : ℕ) : ℝ) ≤ (b : ℝ) ^ ((4 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact h_cast
  have h1 : ((a : ℝ) ^ ((5 : ℕ) : ℝ)) ^ ((1 : ℝ) / 4) ≤ ((b : ℝ) ^ ((4 : ℕ) : ℝ)) ^ ((1 : ℝ) / 4) := by
    exact Real.rpow_le_rpow (by positivity) h_cast' (by norm_num)
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb] at h1
  have h5 : ((5 : ℕ) : ℝ) * (1 / 4) = 5 / 4 := by norm_num
  have h4 : ((4 : ℕ) : ℝ) * (1 / 4) = 1 := by norm_num
  rw [h5, h4, Real.rpow_one] at h1
  exact h1

open scoped Pointwise in
/-- Injectivity and size bounds for sets avoiding geometric progressions in difference squares (Lemma 3.1). -/
theorem difference_squares_avoiding_gp3_bounds (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (A : Finset (ZMod p)) (hA : A.Nonempty)
    (hGP : ¬ has_nondegenerate_gp3 (diff_squares A : Set (ZMod p))) :
    A.card ^ 3 ≤ p ^ 2 ∧
    (A.card : ℝ) ^ (5 / 4 : ℝ) ≤ ((A - A).card : ℝ) ∧
    ∀ (t : ZMod p), t ≠ 0 → t ^ 4 ≠ 1 →
      ∀ (s : ZMod p),
        (((A ×ˢ A).filter (fun (a, b) => b - t * a = s)).card : ℝ) ≤ (p : ℝ) / (A.card : ℝ) := by
  have ht0 : (2 : ZMod p) ≠ 0 := difference_squares_avoiding_gp3_two_ne_zero p hp
  have ht4 : (2 : ZMod p) ^ 4 ≠ 1 := two_pow_four_ne_one_of_prime_ge_seven p hp
  refine ⟨?_, ?_, ?_⟩
  · let f : (ZMod p × (ZMod p × ZMod p)) → ZMod p × ZMod p := fun ⟨a, b, c⟩ => (b - 2 * a, c - 2 * b)
    have h_inj : Set.InjOn f ((A ×ˢ (A ×ˢ A) : Finset _) : Set _) := by
      rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy heq
      rw [Finset.coe_product, Finset.coe_product, Set.mem_prod, Set.mem_prod] at hx hy
      obtain ⟨ha, hb, hc⟩ := hx
      obtain ⟨ha', hb', hc'⟩ := hy
      rw [Finset.mem_coe] at ha hb hc ha' hb' hc'
      injection heq with h1 h2
      obtain ⟨rfl, rfl, rfl⟩ := difference_squares_avoiding_gp3_phi_inj hGP ht0 ht4 ha hb hc ha' hb' hc' h1 h2
      rfl
    have h_maps : Set.MapsTo f ((A ×ˢ (A ×ˢ A) : Finset _) : Set _) ↑(Finset.univ : Finset (ZMod p × ZMod p)) := by
      intro x _
      simp
    have h_card := Finset.card_le_card_of_injOn f h_maps h_inj
    rw [Finset.card_product, Finset.card_product] at h_card
    have h_univ : (Finset.univ : Finset (ZMod p × ZMod p)).card = p ^ 2 := by simp [sq]
    rw [h_univ] at h_card
    calc A.card ^ 3 = A.card * (A.card * A.card) := by ring
    _ ≤ p ^ 2 := h_card
  · obtain ⟨X, hXnonempty, hXA, h_pp⟩ := difference_squares_avoiding_gp3_pluennecke_petridis hA
    let f : (ZMod p × (ZMod p × ZMod p)) → ZMod p × ZMod p := fun ⟨a, b, c⟩ => (b - 2 * a, c - 2 * b)
    let S := A ×ˢ (X ×ˢ X)
    let T := (X - A - A) ×ˢ (X - A - A)
    have h_maps : Set.MapsTo f (S : Set _) (T : Set _) := by
      rintro ⟨a, x1, x2⟩ h
      rw [Finset.coe_product, Finset.coe_product, Set.mem_prod, Set.mem_prod] at h
      obtain ⟨ha, hx1, hx2⟩ := h
      rw [Finset.mem_coe] at ha hx1 hx2
      rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_coe]
      have h1 : x1 - 2 * a ∈ X - A - A := by
        have : 2 * a = a + a := by ring
        rw [this, ← sub_sub]
        exact Finset.sub_mem_sub (Finset.sub_mem_sub hx1 ha) ha
      have h2 : x2 - 2 * x1 ∈ X - A - A := by
        have : 2 * x1 = x1 + x1 := by ring
        rw [this, ← sub_sub]
        exact Finset.sub_mem_sub (Finset.sub_mem_sub hx2 (hXA hx1)) (hXA hx1)
      exact ⟨h1, h2⟩
    have h_inj : Set.InjOn f (S : Set _) := by
      rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy heq
      rw [Finset.coe_product, Finset.coe_product, Set.mem_prod, Set.mem_prod] at hx hy
      obtain ⟨ha, hb, hc⟩ := hx
      obtain ⟨ha', hb', hc'⟩ := hy
      rw [Finset.mem_coe] at ha hb hc ha' hb' hc'
      injection heq with h1 h2
      obtain ⟨rfl, rfl, rfl⟩ := difference_squares_avoiding_gp3_phi_inj hGP ht0 ht4 ha (hXA hb) (hXA hc) ha' (hXA hb') (hXA hc') h1 h2
      rfl
    have h_card := Finset.card_le_card_of_injOn f h_maps h_inj
    rw [Finset.card_product, Finset.card_product, Finset.card_product] at h_card
    have h_inj_bound : A.card * X.card ^ 2 ≤ (X - A - A).card ^ 2 := by
      calc A.card * X.card ^ 2
        _ = A.card * (X.card * X.card) := by ring
        _ ≤ (X - A - A).card * (X - A - A).card := h_card
        _ = (X - A - A).card ^ 2 := by ring
    have hX_pos : 0 < X.card := Finset.card_pos.mpr hXnonempty
    have hX2_pos : 0 < X.card ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero 2 (ne_of_gt hX_pos))
    have h1 : A.card ^ 5 * X.card ^ 2 ≤ (X - A - A).card ^ 2 * A.card ^ 4 := by
      calc A.card ^ 5 * X.card ^ 2
        _ = (A.card * X.card ^ 2) * A.card ^ 4 := by ring
        _ ≤ (X - A - A).card ^ 2 * A.card ^ 4 := Nat.mul_le_mul_right (A.card ^ 4) h_inj_bound
    have h2 : (X - A - A).card ^ 2 * A.card ^ 4 = ((X - A - A).card * A.card ^ 2) ^ 2 := by ring
    have h3 : ((X - A - A).card * A.card ^ 2) ^ 2 ≤ ((A - A).card ^ 2 * X.card) ^ 2 := by
      exact Nat.pow_le_pow_left h_pp 2
    have h4 : ((A - A).card ^ 2 * X.card) ^ 2 = (A - A).card ^ 4 * X.card ^ 2 := by
      rw [mul_pow, ← pow_mul]
    have h5 : A.card ^ 5 * X.card ^ 2 ≤ (A - A).card ^ 4 * X.card ^ 2 := by
      calc A.card ^ 5 * X.card ^ 2
        _ ≤ (X - A - A).card ^ 2 * A.card ^ 4 := h1
        _ = ((X - A - A).card * A.card ^ 2) ^ 2 := h2
        _ ≤ ((A - A).card ^ 2 * X.card) ^ 2 := h3
        _ = (A - A).card ^ 4 * X.card ^ 2 := h4
    have h_pow : A.card ^ 5 ≤ (A - A).card ^ 4 := Nat.le_of_mul_le_mul_right h5 hX2_pos
    exact difference_squares_avoiding_gp3_real_pow h_pow
  · intro t ht0 ht4 s
    let Fs := (A ×ˢ A).filter (fun (a, b) => b - t * a = s)
    let g : (ZMod p × ZMod p) × ZMod p → ZMod p := fun ⟨⟨a, b⟩, c⟩ => c - t * b
    have h_inj : Set.InjOn g ((Fs ×ˢ A : Finset _) : Set _) := by
      rintro ⟨⟨a, b⟩, c⟩ hx ⟨⟨a', b'⟩, c'⟩ hy heq
      rw [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      obtain ⟨⟨⟨ha, hb⟩, hs⟩, hc⟩ := hx
      obtain ⟨⟨⟨ha', hb'⟩, hs'⟩, hc'⟩ := hy
      dsimp [g] at heq
      have h1 : b - t * a = b' - t * a' := by rw [hs, hs']
      obtain ⟨rfl, rfl, rfl⟩ := difference_squares_avoiding_gp3_phi_inj hGP ht0 ht4 ha hb hc ha' hb' hc' h1 heq
      rfl
    have h_maps : Set.MapsTo g ((Fs ×ˢ A : Finset _) : Set _) ↑(Finset.univ : Finset (ZMod p)) := by
      intro x _
      simp
    have h_card := Finset.card_le_card_of_injOn g h_maps h_inj
    rw [Finset.card_product] at h_card
    have h_univ : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p
    rw [h_univ] at h_card
    have hA_pos : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
    have h_cast : (Fs.card : ℝ) * (A.card : ℝ) ≤ (p : ℝ) := by exact_mod_cast h_card
    exact (le_div_iff₀ hA_pos).mpr h_cast
