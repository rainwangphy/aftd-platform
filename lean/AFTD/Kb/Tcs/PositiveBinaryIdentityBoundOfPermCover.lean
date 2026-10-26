import AFTD.Prelude
import AFTD.Kb.Tcs.IsPermCover
import AFTD.Kb.Tcs.EvalBinaryWord
import AFTD.Kb.Tcs.OrderOfMulComm
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.V

/-!
# positive_binary_identity_bound_of_perm_cover

Topic: automata   Node: ef23f9c26213

Provenance: formalization of a published result. Source: arXiv:2610.11098 Lemma 3.6 -- An Improved Lower Bound for Separating Words by Permutation Automata

Let k ≥ 1 be an integer, and let C be a finite set of natural numbers covering the element orders of Equiv.Perm (Fin k) (satisfying is_perm_cover k C). Then there exist distinct binary words u, v : List (Fin 2) with equal counts of each letter (u.count 0 = u.count 1 and v.count 0 = v.count 1) such that eval_binary_word u σ₀ σ₁ = eval_binary_word v σ₀ σ₁ for all σ₀, σ₁ : Equiv.Perm (Fin k), with u.length = v.length, u.length ≤ 2 * 3 ^ (C.card - 1) * C.sup id, and Real.log (u.length : ℝ) ≤ Real.log 2 + ((C.card : ℝ) - 1) * Real.log 3 + Real.log (C.sup id : ℕ).
-/

/-- The binary word spelled by a list of blocks (letter, exponent). -/
def pbi_word (L : List (Fin 2 × ℕ)) : List (Fin 2) := L.flatMap (fun p => List.replicate p.2 p.1)

/-- Positive `d`-inverse of a block list: reverse it and replace each exponent `a` by `d - a % d`. -/
def pbi_inv (d : ℕ) (L : List (Fin 2 × ℕ)) : List (Fin 2 × ℕ) :=
  (L.map (fun p => (p.1, d - p.2 % d))).reverse

/-- One step of the recursion `U' = U C V`, `V' = V C U` with `C` the positive `d`-inverse of `U`. -/
def pbi_step (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)) (d : ℕ) :
    List (Fin 2 × ℕ) × List (Fin 2 × ℕ) :=
  (UV.1 ++ pbi_inv d UV.1 ++ UV.2, UV.2 ++ pbi_inv d UV.1 ++ UV.1)

/-- The substitution `0 ↦ 01`, `1 ↦ 10`. -/
def pbi_subst (w : List (Fin 2)) : List (Fin 2) :=
  w.flatMap (fun x => if x = 0 then [0, 1] else [1, 0])

theorem pbi_eval_append {G : Type*} [Monoid G] (u v : List (Fin 2)) (a b : G) :
    eval_binary_word (u ++ v) a b = eval_binary_word u a b * eval_binary_word v a b := by
  simp [eval_binary_word]

theorem pbi_eval_word_cons {G : Type*} [Monoid G] (p : Fin 2 × ℕ) (L : List (Fin 2 × ℕ)) (a b : G) :
    eval_binary_word (pbi_word (p :: L)) a b = (![a, b] p.1) ^ p.2 * eval_binary_word (pbi_word L) a b := by
  simp [pbi_word, eval_binary_word, List.map_replicate, List.prod_replicate]

theorem pbi_word_append (L L' : List (Fin 2 × ℕ)) : pbi_word (L ++ L') = pbi_word L ++ pbi_word L' := by
  simp [pbi_word]

theorem pbi_eval_word_append {G : Type*} [Monoid G] (L L' : List (Fin 2 × ℕ)) (a b : G) :
    eval_binary_word (pbi_word (L ++ L')) a b =
      eval_binary_word (pbi_word L) a b * eval_binary_word (pbi_word L') a b := by
  rw [pbi_word_append, pbi_eval_append]

theorem pbi_eval_inv {G : Type*} [Group G] (d : ℕ) (hd : 0 < d) (a b : G) (ha : a ^ d = 1)
    (hb : b ^ d = 1) (L : List (Fin 2 × ℕ)) :
    eval_binary_word (pbi_word (pbi_inv d L)) a b = (eval_binary_word (pbi_word L) a b)⁻¹ := by
  have hx : ∀ x : Fin 2, (![a, b] x) ^ d = 1 := by
    intro x; fin_cases x <;> simp [ha, hb]
  induction L with
  | nil => simp [pbi_inv, pbi_word, eval_binary_word]
  | cons p L ih =>
    have hinv : pbi_inv d (p :: L) = pbi_inv d L ++ [(p.1, d - p.2 % d)] := by
      simp [pbi_inv]
    have hsingle : eval_binary_word (pbi_word [(p.1, d - p.2 % d)]) a b
        = (![a, b] p.1) ^ (d - p.2 % d) := by
      simp [pbi_word, eval_binary_word, List.map_replicate, List.prod_replicate]
    rw [hinv, pbi_eval_word_append, ih, hsingle, pbi_eval_word_cons, mul_inv_rev]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    have hm : (![a, b] p.1) ^ p.2 = (![a, b] p.1) ^ (p.2 % d) := by
      conv_lhs => rw [← Nat.div_add_mod p.2 d, pow_add, pow_mul, hx p.1, one_pow, one_mul]
    rw [hm, ← pow_add, Nat.sub_add_cancel (Nat.mod_lt _ hd).le, hx p.1]

/-- The words of a pair are equal at `a, b` whenever `a ^ d = b ^ d = 1` for some positive `d` of `S`. -/
def pbi_good {G : Type*} [Group G] (a b : G) (S : List ℕ)
    (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)) : Prop :=
  ∀ d ∈ S, 0 < d → a ^ d = 1 → b ^ d = 1 →
    eval_binary_word (pbi_word UV.1) a b = eval_binary_word (pbi_word UV.2) a b

theorem pbi_good_step {G : Type*} [Group G] (a b : G) (S : List ℕ)
    (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)) (d : ℕ) (h : pbi_good a b S UV) :
    pbi_good a b (d :: S) (pbi_step UV d) := by
  intro d' hd' hpos ha hb
  simp only [pbi_step, pbi_eval_word_append]
  rcases List.mem_cons.mp hd' with rfl | hmem
  · rw [pbi_eval_inv d' hpos a b ha hb]
    group
  · rw [h d' hmem hpos ha hb]

theorem pbi_good_foldl {G : Type*} [Group G] (a b : G) (ds : List ℕ) :
    ∀ (S : List ℕ) (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)), pbi_good a b S UV →
      pbi_good a b (ds ++ S) (ds.foldl pbi_step UV) := by
  induction ds with
  | nil => intro S UV h; simpa using h
  | cons d ds ih =>
    intro S UV h
    have := ih (d :: S) (pbi_step UV d) (pbi_good_step a b S UV d h)
    intro d' hd' hpos ha hb
    apply this d' _ hpos ha hb
    simp only [List.mem_append, List.mem_cons] at hd' ⊢
    tauto

theorem pbi_word_length (L : List (Fin 2 × ℕ)) : (pbi_word L).length = (L.map Prod.snd).sum := by
  induction L with
  | nil => simp [pbi_word]
  | cons p L ih => simp [pbi_word] at ih ⊢

theorem pbi_word_length_le (L : List (Fin 2 × ℕ)) (M : ℕ) (h : ∀ p ∈ L, p.2 ≤ M) :
    (pbi_word L).length ≤ L.length * M := by
  induction L with
  | nil => simp [pbi_word]
  | cons p L ih =>
    have h1 := h p (by simp)
    have h2 := ih (fun q hq => h q (by simp [hq]))
    rw [pbi_word_length] at h2 ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- The shape invariant after `n` steps. -/
def pbi_shape (d₁ M n : ℕ) (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)) : Prop :=
  UV.1.length = 3 ^ n ∧ UV.2.length = 3 ^ n ∧ (∀ p ∈ UV.1, p.2 ≤ M) ∧ (∀ p ∈ UV.2, p.2 ≤ M) ∧
    (pbi_word UV.1).length = (pbi_word UV.2).length ∧
    (∃ t, UV.1 = (0, d₁) :: t) ∧ (∃ t, UV.2 = (1, d₁) :: t)

theorem pbi_shape_foldl (d₁ M : ℕ) (ds : List ℕ) (hds : ∀ d ∈ ds, d ≤ M) :
    ∀ (n : ℕ) (UV : List (Fin 2 × ℕ) × List (Fin 2 × ℕ)), pbi_shape d₁ M n UV →
      pbi_shape d₁ M (n + ds.length) (ds.foldl pbi_step UV) := by
  induction ds with
  | nil => intro n UV h; simpa using h
  | cons d ds ih =>
    intro n UV h
    have hstep : pbi_shape d₁ M (n + 1) (pbi_step UV d) := by
      obtain ⟨h1, h2, h3, h4, h5, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := h
      have hdM : d ≤ M := hds d (by simp)
      have hinvM : ∀ p ∈ pbi_inv d UV.1, p.2 ≤ M := by
        intro p hp
        simp only [pbi_inv, List.mem_reverse, List.mem_map] at hp
        obtain ⟨q, _, rfl⟩ := hp
        exact le_trans (Nat.sub_le _ _) hdM
      have hinvlen : (pbi_inv d UV.1).length = UV.1.length := by simp [pbi_inv]
      refine ⟨?_, ?_, ?_, ?_, ?_, ⟨t ++ pbi_inv d UV.1 ++ UV.2, ?_⟩, ⟨t' ++ pbi_inv d UV.1 ++ UV.1, ?_⟩⟩
      · simp only [pbi_step, List.length_append, hinvlen, h1, h2]; ring
      · simp only [pbi_step, List.length_append, hinvlen, h1, h2]; ring
      · intro p hp
        simp only [pbi_step, List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · exact h3 p hp
        · exact hinvM p hp
        · exact h4 p hp
      · intro p hp
        simp only [pbi_step, List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · exact h4 p hp
        · exact hinvM p hp
        · exact h3 p hp
      · simp only [pbi_step, pbi_word_append, List.length_append]; omega
      · simp only [pbi_step]; rw [ht]; simp
      · simp only [pbi_step]; rw [ht']; simp
    have := ih (fun d' hd' => hds d' (by simp [hd'])) (n + 1) (pbi_step UV d) hstep
    simp only [List.foldl_cons, List.length_cons]
    have e : n + 1 + ds.length = n + (ds.length + 1) := by omega
    rw [e] at this
    exact this

theorem pbi_eval_subst {G : Type*} [Monoid G] (w : List (Fin 2)) (a b : G) :
    eval_binary_word (pbi_subst w) a b = eval_binary_word w (a * b) (b * a) := by
  induction w with
  | nil => simp [pbi_subst, eval_binary_word]
  | cons x w ih =>
    have hc : pbi_subst (x :: w) = (if x = 0 then [0, 1] else [1, 0]) ++ pbi_subst w := by
      simp [pbi_subst]
    have hc' : (x :: w) = [x] ++ w := rfl
    rw [hc, pbi_eval_append, ih, hc', pbi_eval_append]
    congr 1
    fin_cases x <;> simp [eval_binary_word]

theorem pbi_subst_count (w : List (Fin 2)) :
    (pbi_subst w).count 0 = w.length ∧ (pbi_subst w).count 1 = w.length := by
  induction w with
  | nil => simp [pbi_subst]
  | cons x w ih =>
    have hc : pbi_subst (x :: w) = (if x = 0 then [0, 1] else [1, 0]) ++ pbi_subst w := by
      simp [pbi_subst]
    rw [hc, List.count_append, List.count_append, ih.1, ih.2]
    fin_cases x <;> simp <;> omega

theorem pbi_subst_length (w : List (Fin 2)) : (pbi_subst w).length = 2 * w.length := by
  induction w with
  | nil => simp [pbi_subst]
  | cons x w ih =>
    have hc : pbi_subst (x :: w) = (if x = 0 then [0, 1] else [1, 0]) ++ pbi_subst w := by
      simp [pbi_subst]
    rw [hc, List.length_append, ih]
    fin_cases x <;> simp <;> ring

theorem pbi_subst_cons_word (x : Fin 2) (d : ℕ) (hd : 0 < d) (t : List (Fin 2 × ℕ)) :
    ∃ r, pbi_subst (pbi_word ((x, d) :: t)) = (if x = 0 then [0, 1] else [1, 0]) ++ r := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine ⟨pbi_subst (List.replicate d' x ++ pbi_word t), ?_⟩
  simp [pbi_word, pbi_subst, List.replicate_succ]

/-- Positive binary identity of the symmetric group on k elements constructed from a cover C. -/
theorem positive_binary_identity_bound_of_perm_cover (k : ℕ) (hk : 1 ≤ k) (C : Finset ℕ) (hC : is_perm_cover k C) : ∃ (u v : List (Fin 2)), u ≠ v ∧ u.count 0 = u.count 1 ∧ v.count 0 = v.count 1 ∧ (∀ σ₀ σ₁ : Equiv.Perm (Fin k), eval_binary_word u σ₀ σ₁ = eval_binary_word v σ₀ σ₁) ∧ u.length = v.length ∧ u.length ≤ 2 * 3 ^ (C.card - 1) * C.sup id ∧ Real.log (u.length : ℝ) ≤ Real.log 2 + ((C.card : ℝ) - 1) * Real.log 3 + Real.log (C.sup id : ℕ) := by
  obtain ⟨hpos, hcov⟩ := hC
  obtain ⟨d₀, hd₀, -⟩ := hcov 1
  have hlist : ∃ d₁ ds, C.toList = d₁ :: ds := by
    cases h : C.toList with
    | nil =>
      exfalso
      have : d₀ ∈ C.toList := Finset.mem_toList.mpr hd₀
      rw [h] at this; simp at this
    | cons d₁ ds => exact ⟨d₁, ds, rfl⟩
  obtain ⟨d₁, ds, hl⟩ := hlist
  have hmem : ∀ d, d ∈ C ↔ d = d₁ ∨ d ∈ ds := by
    intro d; rw [← Finset.mem_toList, hl]; simp
  have hd₁C : d₁ ∈ C := (hmem d₁).mpr (Or.inl rfl)
  have hd₁ : 0 < d₁ := hpos d₁ hd₁C
  set M := C.sup id with hM
  have hleM : ∀ d ∈ C, d ≤ M := fun d hd => Finset.le_sup (f := id) hd
  have hcard : C.card = ds.length + 1 := by
    rw [← Finset.length_toList, hl]; simp
  set UV := ds.foldl pbi_step ([((0 : Fin 2), d₁)], [((1 : Fin 2), d₁)]) with hUV
  have hshape0 : pbi_shape d₁ M 0 ([((0 : Fin 2), d₁)], [((1 : Fin 2), d₁)]) := by
    refine ⟨by simp, by simp, ?_, ?_, by simp [pbi_word], ⟨[], rfl⟩, ⟨[], rfl⟩⟩
    · intro p hp; simp at hp; subst hp; exact hleM d₁ hd₁C
    · intro p hp; simp at hp; subst hp; exact hleM d₁ hd₁C
  have hshape := pbi_shape_foldl d₁ M ds (fun d hd => hleM d ((hmem d).mpr (Or.inr hd))) 0 _ hshape0
  rw [← hUV, zero_add] at hshape
  obtain ⟨h1, h2, h3, h4, h5, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := hshape
  refine ⟨pbi_subst (pbi_word UV.1), pbi_subst (pbi_word UV.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := pbi_subst_cons_word 0 d₁ hd₁ t
    obtain ⟨r', hr'⟩ := pbi_subst_cons_word 1 d₁ hd₁ t'
    rw [ht, ht', hr, hr']
    simp
  · rw [(pbi_subst_count _).1, (pbi_subst_count _).2]
  · rw [(pbi_subst_count _).1, (pbi_subst_count _).2]
  · intro σ₀ σ₁
    rw [pbi_eval_subst, pbi_eval_subst]
    obtain ⟨d, hdC, hdvd⟩ := hcov (σ₀ * σ₁)
    have hdvd' : orderOf (σ₁ * σ₀) ∣ d := by rw [← order_of_mul_comm]; exact hdvd
    have hgood0 : pbi_good (σ₀ * σ₁) (σ₁ * σ₀) [d₁] ([((0 : Fin 2), d₁)], [((1 : Fin 2), d₁)]) := by
      intro d' hd' _ ha hb
      simp at hd'; subst hd'
      simp [pbi_word, eval_binary_word, List.map_replicate, List.prod_replicate, ha, hb]
    have hgood := pbi_good_foldl (σ₀ * σ₁) (σ₁ * σ₀) ds [d₁] _ hgood0
    rw [← hUV] at hgood
    apply hgood d _ (hpos d hdC) (orderOf_dvd_iff_pow_eq_one.mp hdvd) (orderOf_dvd_iff_pow_eq_one.mp hdvd')
    rcases (hmem d).mp hdC with h | h
    · simp [h]
    · simp [h]
  · rw [pbi_subst_length, pbi_subst_length, h5]
  · rw [pbi_subst_length, hcard, Nat.add_sub_cancel]
    have := pbi_word_length_le UV.1 M h3
    rw [h1] at this
    calc 2 * (pbi_word UV.1).length ≤ 2 * (3 ^ ds.length * M) := by omega
      _ = 2 * 3 ^ ds.length * M := by ring
  · have hlen := pbi_word_length_le UV.1 M h3
    rw [h1] at hlen
    have hMpos : 0 < M := lt_of_lt_of_le hd₁ (hleM d₁ hd₁C)
    have hupos : 0 < (pbi_subst (pbi_word UV.1)).length := by
      obtain ⟨r, hr⟩ := pbi_subst_cons_word 0 d₁ hd₁ t
      rw [ht, hr]; simp
    have hle : ((pbi_subst (pbi_word UV.1)).length : ℝ) ≤ 2 * (3 : ℝ) ^ ds.length * (M : ℝ) := by
      rw [pbi_subst_length]
      have : 2 * (pbi_word UV.1).length ≤ 2 * 3 ^ ds.length * M := by
        calc 2 * (pbi_word UV.1).length ≤ 2 * (3 ^ ds.length * M) := by omega
          _ = 2 * 3 ^ ds.length * M := by ring
      exact_mod_cast this
    have hcardR : ((C.card : ℝ) - 1) = (ds.length : ℝ) := by
      rw [hcard]; push_cast; ring
    rw [hcardR]
    calc Real.log ((pbi_subst (pbi_word UV.1)).length : ℝ)
        ≤ Real.log (2 * (3 : ℝ) ^ ds.length * (M : ℝ)) :=
          Real.log_le_log (by exact_mod_cast hupos) hle
      _ = Real.log 2 + (ds.length : ℝ) * Real.log 3 + Real.log (M : ℝ) := by
          rw [Real.log_mul (by positivity) (by exact_mod_cast hMpos.ne'),
            Real.log_mul (by norm_num) (by positivity), Real.log_pow]
