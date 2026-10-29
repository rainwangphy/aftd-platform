import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.CardSimpleGraph
import AFTD.Kb.Tcs.IsKstCode

/-!
# k22_code_max_density_two_pow_ge

Topic: combinatorics   Node: 02c16664f8e5

Provenance: helper lemma. step towards four_cycle_graph_code_density_tendsto_one_along_powers_of_two

For every natural number r ≥ 2, the maximum density of a K_{2,2}-code on Fin (2^r) is at least 1 / 2^r.
-/

/-- The edge label `{u,v} ↦ z u * z v`. -/
noncomputable def k22_code_max_density_two_pow_ge_lab {F : Type*} [Field F] {n : ℕ}
    (z : Fin n → F) : Sym2 (Fin n) → F :=
  Sym2.lift ⟨fun a b => z a * z b, fun a b => mul_comm (z a) (z b)⟩

lemma k22_code_max_density_two_pow_ge_lab_mk {F : Type*} [Field F] {n : ℕ} (z : Fin n → F)
    (a b : Fin n) : k22_code_max_density_two_pow_ge_lab z s(a, b) = z a * z b := by
  rw [k22_code_max_density_two_pow_ge_lab, Sym2.lift_mk]

/-- The syndrome of a graph: the sum of the labels of its edges. -/
noncomputable def k22_code_max_density_two_pow_ge_sig {F : Type*} [Field F] {n : ℕ}
    (z : Fin n → F) (G : SimpleGraph (Fin n)) : F :=
  open Classical in
  ∑ e : Sym2 (Fin n), if e ∈ G.edgeSet then k22_code_max_density_two_pow_ge_lab z e else 0

lemma k22_code_max_density_two_pow_ge_sig_symmDiff {F : Type*} [Field F] [CharP F 2] {n : ℕ}
    (z : Fin n → F) (G G' : SimpleGraph (Fin n)) :
    k22_code_max_density_two_pow_ge_sig z (symmDiff G G') =
      k22_code_max_density_two_pow_ge_sig z G + k22_code_max_density_two_pow_ge_sig z G' := by
  unfold k22_code_max_density_two_pow_ge_sig
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hm : e ∈ (symmDiff G G').edgeSet ↔
      (e ∈ G.edgeSet ∧ e ∉ G'.edgeSet) ∨ (e ∈ G'.edgeSet ∧ e ∉ G.edgeSet) := by
    induction e using Sym2.ind with
    | h u v =>
      simp only [SimpleGraph.mem_edgeSet, symmDiff_def, SimpleGraph.sup_adj,
        SimpleGraph.sdiff_adj]
  by_cases h1 : e ∈ G.edgeSet <;> by_cases h2 : e ∈ G'.edgeSet <;>
    simp only [h1, h2, hm, if_true, if_false, not_true, not_false_eq_true, and_true,
      and_false, or_false, false_or, add_zero, zero_add]
  exact (CharTwo.add_self_eq_zero _).symm

lemma k22_code_max_density_two_pow_ge_mem_between {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (e : Sym2 (Fin n)) :
    e ∈ ((⊤ : SimpleGraph (Fin n)).between (↑({a, b} : Finset (Fin n)) : Set (Fin n))
        (↑({c, d} : Finset (Fin n)) : Set (Fin n))).edgeSet ↔
      e ∈ ({s(a, c), s(a, d), s(b, c), s(b, d)} : Finset (Sym2 (Fin n))) := by
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet]
    simp only [SimpleGraph.between_adj, SimpleGraph.top_adj, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    grind

lemma k22_code_max_density_two_pow_ge_sig_between {F : Type*} [Field F] {n : ℕ}
    (z : Fin n → F) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    k22_code_max_density_two_pow_ge_sig z
        ((⊤ : SimpleGraph (Fin n)).between (↑({a, b} : Finset (Fin n)) : Set (Fin n))
          (↑({c, d} : Finset (Fin n)) : Set (Fin n))) =
      (z a + z b) * (z c + z d) := by
  classical
  unfold k22_code_max_density_two_pow_ge_sig
  simp only [k22_code_max_density_two_pow_ge_mem_between a b c d hab hac had hbc hbd hcd]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; grind),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; grind),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; grind),
    Finset.sum_singleton]
  simp only [k22_code_max_density_two_pow_ge_lab_mk]
  ring

/-- Every fibre of the syndrome map is a `K_{2,2}`-code, when the labels are injective in
characteristic 2. -/
lemma k22_code_max_density_two_pow_ge_fiber_code {F : Type*} [Field F] [CharP F 2] {n : ℕ}
    (z : Fin n → F) (hz : Function.Injective z) (s : F) :
    is_kst_code 2 2 n {G | k22_code_max_density_two_pow_ge_sig z G = s} := by
  intro G G' hG hG' _ A B hAB hA hB heq
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hB
  have hdist : ∀ x ∈ ({a, b} : Finset (Fin n)), ∀ y ∈ ({c, d} : Finset (Fin n)), x ≠ y :=
    Finset.disjoint_iff_ne.mp hAB
  have hac : a ≠ c := hdist a (by simp) c (by simp)
  have had : a ≠ d := hdist a (by simp) d (by simp)
  have hbc : b ≠ c := hdist b (by simp) c (by simp)
  have hbd : b ≠ d := hdist b (by simp) d (by simp)
  have h1 : z a + z b ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact hab (hz h)
  have h2 : z c + z d ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact hcd (hz h)
  have hsd := k22_code_max_density_two_pow_ge_sig_symmDiff z G G'
  rw [heq, k22_code_max_density_two_pow_ge_sig_between z a b c d hab hac had hbc hbd hcd] at hsd
  simp only [Set.mem_setOf_eq] at hG hG'
  rw [hG, hG', CharTwo.add_self_eq_zero] at hsd
  exact mul_ne_zero h1 h2 hsd

lemma k22_code_max_density_two_pow_ge_r_le_choose (r : ℕ) (hr : 2 ≤ r) :
    r ≤ (2 ^ r).choose 2 := by
  have h2r : 2 * r ≤ 2 ^ r := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have : 2 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      rw [pow_succ]; omega
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 2 ≤ 2 ^ r - 1 := by omega
  calc r * 2 ≤ 2 ^ r := by omega
    _ = 2 ^ r * 1 := (mul_one _).symm
    _ ≤ 2 ^ r * (2 ^ r - 1) := Nat.mul_le_mul_left _ (by omega)

/-- For every natural number r ≥ 2, the maximum density of a K_{2,2}-code on Fin (2^r) is at least 1 / 2^r. -/
theorem k22_code_max_density_two_pow_ge (r : ℕ) (hr : 2 ≤ r) :
    1 / ((2 : ℝ) ^ r) ≤ kst_code_max_density 2 2 (2 ^ r) := by
  classical
  letI : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 r) = 2 ^ r := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 r (by omega)
  have hcardV : Fintype.card (Fin (2 ^ r)) = 2 ^ r := Fintype.card_fin _
  let e : Fin (2 ^ r) ≃ GaloisField 2 r := (Fintype.equivFinOfCardEq hcard).symm
  set N := (2 ^ r).choose 2 with hN
  have hrN := k22_code_max_density_two_pow_ge_r_le_choose r hr
  obtain ⟨s, hs⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := k22_code_max_density_two_pow_ge_sig (fun v => e v)) (n := 2 ^ (N - r)) (by
      rw [hcard, card_simpleGraph, hcardV, ← pow_add, Nat.add_sub_cancel' hrN])
  set C : Set (SimpleGraph (Fin (2 ^ r))) :=
    {G | k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s} with hC
  have hcode : is_kst_code 2 2 (2 ^ r) C :=
    k22_code_max_density_two_pow_ge_fiber_code _ e.injective s
  have hncard : 2 ^ (N - r) ≤ C.ncard := by
    have : C = ↑(Finset.univ.filter
        fun G => k22_code_max_density_two_pow_ge_sig (fun v => e v) G = s) := by
      ext G; simp [hC]
    rw [this, Set.ncard_coe_finset]
    exact hs
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have hval : 1 / ((2 : ℝ) ^ r) ≤ (C.ncard : ℝ) / 2 ^ N := by
    rw [div_le_div_iff₀ (by positivity) hpos, one_mul]
    calc (2 : ℝ) ^ N = (2 : ℝ) ^ (N - r) * 2 ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hrN]
      _ ≤ (C.ncard : ℝ) * 2 ^ r := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hncard
  have hbdd : BddAbove (Set.range fun D : Set (SimpleGraph (Fin (2 ^ r))) =>
      ⨆ (_ : is_kst_code 2 2 (2 ^ r) D), (D.ncard : ℝ) / 2 ^ N) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨D, rfl⟩
    refine Real.iSup_le (fun _ => ?_) zero_le_one
    rw [div_le_one hpos]
    have h1 : D.ncard ≤ 2 ^ N := by
      calc D.ncard ≤ (Set.univ : Set (SimpleGraph (Fin (2 ^ r)))).ncard :=
            Set.ncard_le_ncard (Set.subset_univ D)
        _ = 2 ^ N := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_simpleGraph, hcardV]
    exact_mod_cast h1
  unfold kst_code_max_density
  refine le_trans hval (le_trans ?_ (le_ciSup hbdd C))
  rw [ciSup_pos hcode]
