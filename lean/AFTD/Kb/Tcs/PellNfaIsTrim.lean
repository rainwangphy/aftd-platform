import AFTD.Prelude
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.NfaIsTrim

/-!
# pell_nfa_is_trim

Topic: automata   Node: e98363029584

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

The n-state Pell NFA pell_nfa n is trim: every state is reachable from the start state and can reach an accept state.
-/

/-- The letter of the `p`-th chain step: `2` from the first state, `p % 5` above. -/
def pell_nfa_is_trim_letter (p : ℕ) : Fin 5 := if p = 0 then 2 else ⟨p % 5, Nat.mod_lt p (by norm_num)⟩

/-- A single chain step: from a state of value `p` the letter `pell_nfa_is_trim_letter p` reaches any
state of value `p + 1`. -/
theorem pell_nfa_is_trim_step_succ (n p : ℕ) (hn : 3 ≤ n) (hp : p + 1 < n) :
    ∀ (s q : Fin n), s.val = p → q.val = p + 1 →
      q ∈ (pell_nfa n).step s (pell_nfa_is_trim_letter p) := by
  intro s q hs hq
  simp only [pell_nfa, pell_nfa_is_trim_letter, Set.mem_ofPred_eq]
  rw [hs, hq]
  by_cases hp0 : p = 0
  · rw [hp0]
    refine ⟨1, by norm_num, by omega, ?_⟩
    norm_num
  · refine ⟨p, by omega, by omega, ?_⟩
    simp only [if_neg hp0]
    simp

/-- From a state of value `p` one reaches any state of value `p + m` by walking the chain. -/
theorem pell_nfa_is_trim_reach_fwd (n : ℕ) (hn : 3 ≤ n) : ∀ (m p : ℕ), p + m < n →
    ∀ (s q : Fin n), s.val = p → q.val = p + m →
      ∃ w, q ∈ (pell_nfa n).evalFrom {s} w := by
  intro m
  induction m with
  | zero =>
    intro p hp s q hs hq
    exact ⟨[], by simp only [NFA.evalFrom_nil, Set.mem_singleton_iff]; exact Fin.ext (by omega)⟩
  | succ m ih =>
    intro p hp s q hs hq
    have hpm : p + m < n := by omega
    obtain ⟨w, hw⟩ := ih p hpm s ⟨p + m, hpm⟩ hs rfl
    have hstep : q ∈ (pell_nfa n).step ⟨p + m, hpm⟩ (pell_nfa_is_trim_letter (p + m)) := by
      refine pell_nfa_is_trim_step_succ n (p + m) hn (by omega) _ q rfl ?_
      show (↑q : ℕ) = p + m + 1
      omega
    refine ⟨w ++ [pell_nfa_is_trim_letter (p + m)], ?_⟩
    simp only [NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
    exact ⟨_, hw, hstep⟩

/-- The n-state Pell NFA pell_nfa n is trim for n ≥ 3. -/
theorem pell_nfa_is_trim (n : ℕ) (hn : 3 ≤ n) : nfa_is_trim (pell_nfa n) := by
  intro q
  constructor
  · obtain ⟨w, hw⟩ := pell_nfa_is_trim_reach_fwd n hn q.val 0 (by omega) ⟨0, by omega⟩ q rfl (by omega)
    exact ⟨w, NFA.mem_evalFrom_iff_exists.mpr ⟨⟨0, by omega⟩, rfl, hw⟩⟩
  · obtain ⟨w, hw⟩ := pell_nfa_is_trim_reach_fwd n hn (n - 1 - q.val) q.val (by omega) q
      ⟨n - 1, by omega⟩ rfl (by simp; omega)
    exact ⟨w, ⟨n - 1, by omega⟩, by show (n - 1) + 1 = n; omega, hw⟩
