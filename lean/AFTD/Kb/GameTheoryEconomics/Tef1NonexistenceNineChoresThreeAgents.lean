import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTef1
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.ChorePrefixBundle

/-!
# tef1_nonexistence_nine_chores_three_agents

Topic: fair_division   Node: 5ac7d1030f84

Provenance: formalization of a published result. Source: arXiv:2611.25892 Thm. 3.1

There exists a cost matrix d : Fin 3 → Fin 9 → ℝ with all costs nonnegative (∀ i c, 0 ≤ d i c) such that for every allocation π : Fin 9 → Fin 3, π is not temporal EF1 (¬ is_tef1 3 9 d π).
-/

inductive tef1_nonexistence_nine_chores_three_agents_FailTree where
  | fail (t : Fin 9) (i j : Fin 3) : tef1_nonexistence_nine_chores_three_agents_FailTree
  | branch (f0 f1 f2 : tef1_nonexistence_nine_chores_three_agents_FailTree) : tef1_nonexistence_nine_chores_three_agents_FailTree

def tef1_nonexistence_nine_chores_three_agents_d_costs : Fin 3 → Fin 9 → ℕ
  | 0 => ![2, 1, 2, 2, 8, 8, 4, 8, 8]
  | 1 => ![2, 3, 1, 3, 3, 5, 5, 5, 5]
  | 2 => ![5, 2, 1, 2, 10, 5, 10, 10, 10]

def tef1_nonexistence_nine_chores_three_agents_d_real (i : Fin 3) (c : Fin 9) : ℝ :=
  (tef1_nonexistence_nine_chores_three_agents_d_costs i c : ℝ)

def tef1_nonexistence_nine_chores_three_agents_p_bundle (p : List (Fin 3)) (t : Fin 9) (a : Fin 3) : Finset (Fin 9) :=
  Finset.filter (fun c : Fin 9 => c ≤ t ∧ p[c.val]? = some a) Finset.univ

def tef1_nonexistence_nine_chores_three_agents_p_val (p : List (Fin 3)) (t : Fin 9) (i a : Fin 3) : ℕ :=
  ∑ c ∈ tef1_nonexistence_nine_chores_three_agents_p_bundle p t a, tef1_nonexistence_nine_chores_three_agents_d_costs i c

def tef1_nonexistence_nine_chores_three_agents_check_leaf (p : List (Fin 3)) (t : Fin 9) (i j : Fin 3) : Bool :=
  decide (i ≠ j ∧ t.val < p.length ∧
    let vi := tef1_nonexistence_nine_chores_three_agents_p_val p t i i
    let vj := tef1_nonexistence_nine_chores_three_agents_p_val p t i j
    vj < vi ∧ ∀ c ∈ tef1_nonexistence_nine_chores_three_agents_p_bundle p t i, vj < vi - tef1_nonexistence_nine_chores_three_agents_d_costs i c)

def tef1_nonexistence_nine_chores_three_agents_find_witness (p : List (Fin 3)) : Option (Fin 9 × Fin 3 × Fin 3) :=
  if h : p.length > 0 ∧ p.length ≤ 9 then
    let t : Fin 9 := ⟨p.length - 1, by omega⟩
    let pairs : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
    pairs.findSome? (fun (i, j) => if tef1_nonexistence_nine_chores_three_agents_check_leaf p t i j then some (t, i, j) else none)
  else none

def tef1_nonexistence_nine_chores_three_agents_make_tree : ℕ → List (Fin 3) → tef1_nonexistence_nine_chores_three_agents_FailTree
  | n, p =>
    match tef1_nonexistence_nine_chores_three_agents_find_witness p with
    | some (t, i, j) => tef1_nonexistence_nine_chores_three_agents_FailTree.fail t i j
    | none =>
      match n with
      | 0 => tef1_nonexistence_nine_chores_three_agents_FailTree.fail 0 0 1
      | n + 1 => tef1_nonexistence_nine_chores_three_agents_FailTree.branch
          (tef1_nonexistence_nine_chores_three_agents_make_tree n (p ++ [0]))
          (tef1_nonexistence_nine_chores_three_agents_make_tree n (p ++ [1]))
          (tef1_nonexistence_nine_chores_three_agents_make_tree n (p ++ [2]))

def tef1_nonexistence_nine_chores_three_agents_the_tree : tef1_nonexistence_nine_chores_three_agents_FailTree :=
  tef1_nonexistence_nine_chores_three_agents_make_tree 9 []

def tef1_nonexistence_nine_chores_three_agents_verify_tree : tef1_nonexistence_nine_chores_three_agents_FailTree → List (Fin 3) → Bool
  | tef1_nonexistence_nine_chores_three_agents_FailTree.fail t i j, p => tef1_nonexistence_nine_chores_three_agents_check_leaf p t i j
  | tef1_nonexistence_nine_chores_three_agents_FailTree.branch f0 f1 f2, p =>
    decide (p.length < 9) &&
    tef1_nonexistence_nine_chores_three_agents_verify_tree f0 (p ++ [0]) &&
    tef1_nonexistence_nine_chores_three_agents_verify_tree f1 (p ++ [1]) &&
    tef1_nonexistence_nine_chores_three_agents_verify_tree f2 (p ++ [2])

lemma tef1_nonexistence_nine_chores_three_agents_not_is_tef1_of_witness {d : Fin 3 → Fin 9 → ℝ} {π : Fin 9 → Fin 3}
    (t : Fin 9) (i j : Fin 3) (hij : i ≠ j)
    (h1 : additive_valuation (d i) (chore_prefix_bundle π t j) < additive_valuation (d i) (chore_prefix_bundle π t i))
    (h2 : ∀ c ∈ chore_prefix_bundle π t i,
      additive_valuation (d i) (chore_prefix_bundle π t j) < additive_valuation (d i) (chore_prefix_bundle π t i) - d i c) :
    ¬ is_tef1 3 9 d π := by
  intro htef1
  have h := htef1 t i j hij
  rcases h with hle | ⟨c, hc, hle⟩
  · linarith
  · have hc2 := h2 c hc
    linarith

lemma tef1_nonexistence_nine_chores_three_agents_chore_prefix_bundle_eq_p_bundle
    (π : Fin 9 → Fin 3) (p : List (Fin 3)) (t : Fin 9) (a : Fin 3)
    (ht : t.val < p.length)
    (hp : ∀ c : Fin 9, c.val < p.length → p[c.val]? = some (π c)) :
    chore_prefix_bundle π t a = tef1_nonexistence_nine_chores_three_agents_p_bundle p t a := by
  ext c
  simp only [chore_prefix_bundle, tef1_nonexistence_nine_chores_three_agents_p_bundle, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hct, hcπ⟩
    have hclt : c.val < p.length := lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hct) ht
    rw [hp c hclt, hcπ]
    exact ⟨hct, rfl⟩
  · rintro ⟨hct, hcp⟩
    have hclt : c.val < p.length := lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hct) ht
    have := hp c hclt
    rw [hcp] at this
    exact ⟨hct, Option.some.inj this.symm⟩

lemma tef1_nonexistence_nine_chores_three_agents_additive_valuation_eq_p_val (p : List (Fin 3)) (t : Fin 9) (i a : Fin 3) :
    additive_valuation (tef1_nonexistence_nine_chores_three_agents_d_real i) (tef1_nonexistence_nine_chores_three_agents_p_bundle p t a) =
    (tef1_nonexistence_nine_chores_three_agents_p_val p t i a : ℝ) := by
  simp only [additive_valuation, tef1_nonexistence_nine_chores_three_agents_d_real,
             tef1_nonexistence_nine_chores_three_agents_p_val, Nat.cast_sum]

lemma tef1_nonexistence_nine_chores_three_agents_nat_cast_sub_lt {a b c : ℕ} (h : a < b - c) : (a : ℝ) < (b : ℝ) - (c : ℝ) := by
  have hcb : c ≤ b := by omega
  rw [← Nat.cast_sub hcb]
  exact Nat.cast_lt.mpr h

lemma tef1_nonexistence_nine_chores_three_agents_prefix_extend (π : Fin 9 → Fin 3) (p : List (Fin 3)) (hlen : p.length < 9)
    (hp : ∀ c : Fin 9, c.val < p.length → p[c.val]? = some (π c))
    (a : Fin 3) (h_ext : π ⟨p.length, hlen⟩ = a) :
    ∀ c : Fin 9, c.val < (p ++ [a]).length → (p ++ [a])[c.val]? = some (π c) := by
  intro c hc
  rw [List.length_append, List.length_singleton] at hc
  rcases lt_or_eq_of_le (Nat.le_of_lt_add_one hc) with hlt | heq
  · rw [List.getElem?_append_left hlt]
    exact hp c hlt
  · have hc_eq : c = ⟨p.length, hlen⟩ := Fin.ext heq
    subst hc_eq
    rw [List.getElem?_append_right (le_refl _)]
    simp [h_ext]

theorem tef1_nonexistence_nine_chores_three_agents_tree_sound
    (tree : tef1_nonexistence_nine_chores_three_agents_FailTree) (p : List (Fin 3))
    (h_tree : tef1_nonexistence_nine_chores_three_agents_verify_tree tree p = true)
    (π : Fin 9 → Fin 3)
    (hp : ∀ c : Fin 9, c.val < p.length → p[c.val]? = some (π c)) :
    ¬ is_tef1 3 9 tef1_nonexistence_nine_chores_three_agents_d_real π := by
  induction tree generalizing p with
  | fail t i j =>
    dsimp [tef1_nonexistence_nine_chores_three_agents_verify_tree] at h_tree
    have h_dec := of_decide_eq_true h_tree
    rcases h_dec with ⟨hij, ht, hlt, hall⟩
    have hbi := tef1_nonexistence_nine_chores_three_agents_chore_prefix_bundle_eq_p_bundle π p t i ht hp
    have hbj := tef1_nonexistence_nine_chores_three_agents_chore_prefix_bundle_eq_p_bundle π p t j ht hp
    apply tef1_nonexistence_nine_chores_three_agents_not_is_tef1_of_witness t i j hij
    · rw [hbi, hbj]
      repeat rw [tef1_nonexistence_nine_chores_three_agents_additive_valuation_eq_p_val]
      exact Nat.cast_lt.mpr hlt
    · intro c hc
      rw [hbi] at hc
      rw [hbi, hbj]
      repeat rw [tef1_nonexistence_nine_chores_three_agents_additive_valuation_eq_p_val]
      dsimp [tef1_nonexistence_nine_chores_three_agents_d_real]
      exact tef1_nonexistence_nine_chores_three_agents_nat_cast_sub_lt (hall c hc)
  | branch f0 f1 f2 ih0 ih1 ih2 =>
    dsimp [tef1_nonexistence_nine_chores_three_agents_verify_tree] at h_tree
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_tree
    rcases h_tree with ⟨⟨⟨hlen, h0⟩, h1⟩, h2⟩
    let k : Fin 9 := ⟨p.length, hlen⟩
    generalize h : π k = val
    revert h
    fin_cases val
    · intro h
      exact ih0 (p ++ [0]) h0 (tef1_nonexistence_nine_chores_three_agents_prefix_extend π p hlen hp 0 h)
    · intro h
      exact ih1 (p ++ [1]) h1 (tef1_nonexistence_nine_chores_three_agents_prefix_extend π p hlen hp 1 h)
    · intro h
      exact ih2 (p ++ [2]) h2 (tef1_nonexistence_nine_chores_three_agents_prefix_extend π p hlen hp 2 h)

theorem tef1_nonexistence_nine_chores_three_agents_the_tree_verified :
    tef1_nonexistence_nine_chores_three_agents_verify_tree tef1_nonexistence_nine_chores_three_agents_the_tree [] = true := by
  rfl

/-- Nine chores suffice for nonexistence of a TEF1 allocation with three agents. -/
theorem tef1_nonexistence_nine_chores_three_agents :
    ∃ (d : Fin 3 → Fin 9 → ℝ), (∀ i c, 0 ≤ d i c) ∧ ∀ π : Fin 9 → Fin 3, ¬ is_tef1 3 9 d π := by
  use tef1_nonexistence_nine_chores_three_agents_d_real
  refine ⟨?_, ?_⟩
  · intros i c
    exact Nat.cast_nonneg _
  · intro π
    exact tef1_nonexistence_nine_chores_three_agents_tree_sound
      tef1_nonexistence_nine_chores_three_agents_the_tree []
      tef1_nonexistence_nine_chores_three_agents_the_tree_verified π
      (by intro c hc; contradiction)
