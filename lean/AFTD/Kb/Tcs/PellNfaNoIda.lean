import AFTD.Prelude
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.NfaCompliesIda
import AFTD.Kb.Tcs.PellNfaStepTable

/-!
# pell_nfa_no_ida

Topic: automata   Node: 485c0f86363d

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

The Pell automaton A_n does not comply with IDA: there are no distinct states p, q and no word v such that p is reachable from p by v, q from p by v, and q from q by v.
-/

lemma pell_nfa_no_ida_evalFrom_le (n : ℕ) {v : List (Fin 5)} {p q : Fin n}
    (h : q ∈ (pell_nfa n).evalFrom {p} v) : (p : ℕ) ≤ (q : ℕ) := by
  induction v generalizing p with
  | nil =>
    simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at h
    subst h
    exact le_rfl
  | cons a v ih =>
    rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists] at h
    rcases h with ⟨m, hm, hq⟩
    rw [NFA.stepSet, Set.mem_iUnion] at hm
    rcases hm with ⟨p', hp'⟩
    rw [Set.mem_iUnion] at hp'
    rcases hp' with ⟨hp_eq, hm_step⟩
    simp only [Set.mem_singleton_iff] at hp_eq
    subst hp_eq
    have h1 : (p' : ℕ) ≤ (m : ℕ) := by
      have := pell_nfa_step_table n hm_step
      rcases this with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega
    have h2 := ih hq
    omega

lemma pell_nfa_no_ida_step_self (n : ℕ) {p : Fin n} {k : Fin 5}
    (h : p ∈ (pell_nfa n).step p k) :
    (k : ℕ) = (p : ℕ) % 5 ∨ (k : ℕ) = ((p : ℕ) + 1) % 5 := by
  have := pell_nfa_step_table n h
  rcases this with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, hq⟩
  · left; exact hk
  · right; exact hk
  · rcases hq with h | h <;> omega

lemma pell_nfa_no_ida_evalFrom_self_cons (n : ℕ) {a : Fin 5} {v : List (Fin 5)} {p : Fin n}
    (h : p ∈ (pell_nfa n).evalFrom {p} (a :: v)) :
    p ∈ (pell_nfa n).step p a ∧ p ∈ (pell_nfa n).evalFrom {p} v := by
  rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists] at h
  rcases h with ⟨m, hm, hq⟩
  rw [NFA.stepSet, Set.mem_iUnion] at hm
  rcases hm with ⟨p', hp'⟩
  rw [Set.mem_iUnion] at hp'
  rcases hp' with ⟨hp_eq, hm_step⟩
  simp only [Set.mem_singleton_iff] at hp_eq
  subst hp_eq
  have h1 : (p' : ℕ) ≤ (m : ℕ) := by
    have := pell_nfa_step_table n hm_step
    rcases this with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega
  have h2 : (m : ℕ) ≤ (p' : ℕ) := pell_nfa_no_ida_evalFrom_le n hq
  have h_eq : m = p' := Fin.ext (by omega)
  subst h_eq
  exact ⟨hm_step, hq⟩

lemma pell_nfa_no_ida_evalFrom_self_letters (n : ℕ) {v : List (Fin 5)} {p : Fin n}
    (h : p ∈ (pell_nfa n).evalFrom {p} v) :
    ∀ k ∈ v, (k : ℕ) = (p : ℕ) % 5 ∨ (k : ℕ) = ((p : ℕ) + 1) % 5 := by
  induction v with
  | nil => intros k hk; contradiction
  | cons a v ih =>
    intros k hk
    obtain ⟨ha_step, hp_v⟩ := pell_nfa_no_ida_evalFrom_self_cons n h
    rcases List.mem_cons.mp hk with rfl | hk_v
    · exact pell_nfa_no_ida_step_self n ha_step
    · exact ih hp_v k hk_v

lemma pell_nfa_no_ida_step_in_range (n : ℕ) {p s t : Fin n} {k : Fin 5}
    (hs : (s : ℕ) = (p : ℕ) ∨ (s : ℕ) = (p : ℕ) + 1 ∨ (s : ℕ) = (p : ℕ) + 2)
    (hk : (k : ℕ) = (p : ℕ) % 5 ∨ (k : ℕ) = ((p : ℕ) + 1) % 5)
    (h_step : t ∈ (pell_nfa n).step s k) :
    (t : ℕ) = (p : ℕ) ∨ (t : ℕ) = (p : ℕ) + 1 ∨ (t : ℕ) = (p : ℕ) + 2 := by
  have := pell_nfa_step_table n h_step
  rcases this with ⟨hk', ht⟩ | ⟨hk', ht⟩ | ⟨hk', ht⟩ <;>
    rcases hs with hs | hs | hs <;>
    rcases hk with hk | hk <;>
    rcases ht with ht | ht <;>
    omega

lemma pell_nfa_no_ida_evalFrom_in_range (n : ℕ) {p : Fin n} {v : List (Fin 5)}
    (hv : ∀ k ∈ v, (k : ℕ) = (p : ℕ) % 5 ∨ (k : ℕ) = ((p : ℕ) + 1) % 5)
    {s t : Fin n}
    (hs : (s : ℕ) = (p : ℕ) ∨ (s : ℕ) = (p : ℕ) + 1 ∨ (s : ℕ) = (p : ℕ) + 2)
    (ht : t ∈ (pell_nfa n).evalFrom {s} v) :
    (t : ℕ) = (p : ℕ) ∨ (t : ℕ) = (p : ℕ) + 1 ∨ (t : ℕ) = (p : ℕ) + 2 := by
  induction v generalizing s with
  | nil =>
    simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at ht
    subst ht
    exact hs
  | cons a v ih =>
    rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists] at ht
    rcases ht with ⟨m, hm, ht⟩
    rw [NFA.stepSet, Set.mem_iUnion] at hm
    rcases hm with ⟨s', hs'⟩
    rw [Set.mem_iUnion] at hs'
    rcases hs' with ⟨hs_eq, hm_step⟩
    simp only [Set.mem_singleton_iff] at hs_eq
    subst hs_eq
    have ha : (a : ℕ) = (p : ℕ) % 5 ∨ (a : ℕ) = ((p : ℕ) + 1) % 5 :=
      hv a List.mem_cons_self
    have hm_range := pell_nfa_no_ida_step_in_range n hs ha hm_step
    have hv' : ∀ k ∈ v, (k : ℕ) = (p : ℕ) % 5 ∨ (k : ℕ) = ((p : ℕ) + 1) % 5 :=
      fun k hk => hv k (List.mem_cons_of_mem a hk)
    exact ih hv' hm_range ht

lemma pell_nfa_no_ida_step_p_plus_1_letter (n : ℕ) {p s t : Fin n} {k : Fin 5}
    (hs : (s : ℕ) = (p : ℕ) ∨ (s : ℕ) = (p : ℕ) + 2)
    (hk : (k : ℕ) = ((p : ℕ) + 1) % 5)
    (h_step : t ∈ (pell_nfa n).step s k) :
    (t : ℕ) = (p : ℕ) ∨ (t : ℕ) = (p : ℕ) + 2 := by
  have := pell_nfa_step_table n h_step
  rcases this with ⟨hk', ht⟩ | ⟨hk', ht⟩ | ⟨hk', ht⟩ <;>
    rcases hs with hs | hs <;>
    rcases ht with ht | ht <;>
    omega

lemma pell_nfa_no_ida_evalFrom_p_plus_1_letters (n : ℕ) {p : Fin n} {v : List (Fin 5)}
    (hv : ∀ k ∈ v, (k : ℕ) = ((p : ℕ) + 1) % 5)
    {s t : Fin n}
    (hs : (s : ℕ) = (p : ℕ) ∨ (s : ℕ) = (p : ℕ) + 2)
    (ht : t ∈ (pell_nfa n).evalFrom {s} v) :
    (t : ℕ) = (p : ℕ) ∨ (t : ℕ) = (p : ℕ) + 2 := by
  induction v generalizing s with
  | nil =>
    simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at ht
    subst ht
    exact hs
  | cons a v ih =>
    rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists] at ht
    rcases ht with ⟨m, hm, ht⟩
    rw [NFA.stepSet, Set.mem_iUnion] at hm
    rcases hm with ⟨s', hs'⟩
    rw [Set.mem_iUnion] at hs'
    rcases hs' with ⟨hs_eq, hm_step⟩
    simp only [Set.mem_singleton_iff] at hs_eq
    subst hs_eq
    have ha : (a : ℕ) = ((p : ℕ) + 1) % 5 :=
      hv a List.mem_cons_self
    have hm_range := pell_nfa_no_ida_step_p_plus_1_letter n hs ha hm_step
    have hv' : ∀ k ∈ v, (k : ℕ) = ((p : ℕ) + 1) % 5 :=
      fun k hk => hv k (List.mem_cons_of_mem a hk)
    exact ih hv' hm_range ht

/-- A_n does not comply with IDA: no single word v can carry q_p → q_p, q_p → q_q and q_q → q_q with p ≠ q, because letters that keep the state fixed at index p are dead two places to the right. -/
theorem pell_nfa_no_ida (n : ℕ) : ¬ nfa_complies_ida (pell_nfa n) := by
  intro h_ida
  rcases h_ida with ⟨p, q, hpq, v, hp_v, hqp_v, hq_v⟩
  cases v with
  | nil =>
    simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at hqp_v
    exact hpq hqp_v.symm
  | cons a v =>
    have h_le : (p : ℕ) ≤ (q : ℕ) := pell_nfa_no_ida_evalFrom_le n hqp_v
    have h_lt : (p : ℕ) < (q : ℕ) := by
      rcases eq_or_lt_of_le h_le with heq | hlt
      · exfalso; exact hpq (Fin.ext heq)
      · exact hlt
    have hv_p := pell_nfa_no_ida_evalFrom_self_letters n hp_v
    have h_range := pell_nfa_no_ida_evalFrom_in_range n hv_p (Or.inl rfl) hqp_v
    have h_q_val : (q : ℕ) = (p : ℕ) + 1 ∨ (q : ℕ) = (p : ℕ) + 2 := by
      rcases h_range with h1 | h2 | h3 <;> omega
    rcases h_q_val with h_plus_1 | h_plus_2
    · have hv_q := pell_nfa_no_ida_evalFrom_self_letters n hq_v
      have hv_all : ∀ k ∈ a :: v, (k : ℕ) = ((p : ℕ) + 1) % 5 := by
        intro k hk
        have hk_p := hv_p k hk
        have hk_q := hv_q k hk
        omega
      have h_q_res := pell_nfa_no_ida_evalFrom_p_plus_1_letters n hv_all (Or.inl rfl) hqp_v
      omega
    · obtain ⟨hp_step, -⟩ := pell_nfa_no_ida_evalFrom_self_cons n hp_v
      obtain ⟨hq_step, -⟩ := pell_nfa_no_ida_evalFrom_self_cons n hq_v
      have h_step_p := pell_nfa_step_table n hp_step
      have h_step_q := pell_nfa_step_table n hq_step
      omega
