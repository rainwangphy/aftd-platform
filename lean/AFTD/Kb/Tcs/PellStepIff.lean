import AFTD.Prelude
import AFTD.Kb.Tcs.PellNfa

/-!
# pell_step_iff

Topic: automata   Node: 84536f3e3f3c

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

Closed form of the transitions of A_n: q is reachable from p in one step on letter k iff one of five explicit arithmetic conditions holds (letter k congruent to p, p+1 or p+2 mod 5, with the state bounds of the gadget and the two boundary cases where the top of the chain is reached).
-/

/-- Explicit closed form of the transition relation of the Pell automaton. -/
theorem pell_step_iff (n : ℕ) (hn : 3 ≤ n) {p q : Fin n} {k : Fin 5} :
    q ∈ (pell_nfa n).step p k ↔
      (k.val = p.val % 5 ∧ 1 ≤ p.val ∧ p.val + 2 ≤ n ∧ (q.val = p.val ∨ q.val = p.val + 1)) ∨
      (k.val = p.val % 5 ∧ p.val + 1 = n ∧ q.val = p.val) ∨
      (k.val = (p.val + 1) % 5 ∧ p.val + 3 ≤ n ∧ (q.val = p.val ∨ q.val = p.val + 2)) ∨
      (k.val = (p.val + 1) % 5 ∧ p.val + 2 = n ∧ q.val = p.val) ∨
      (k.val = (p.val + 2) % 5 ∧ p.val + 3 ≤ n ∧ (q.val = p.val + 1 ∨ q.val = p.val + 2)) := by
  constructor
  · intro h
    simp only [pell_nfa] at h
    obtain ⟨i, hi1, hi2, h⟩ := h
    rcases h with ⟨hk, hpq⟩ | ⟨hk, hpq⟩
    · rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · right; right; left
        exact ⟨by omega, by omega, by rcases hq with h | h <;> omega⟩
      · left
        exact ⟨by omega, by omega, by omega, by rcases hq with h | h <;> omega⟩
    · rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
      · by_cases hb : p.val + 2 = n
        · right; right; right; left
          exact ⟨by omega, by omega, by omega⟩
        · right; right; left
          exact ⟨by omega, by omega, by omega⟩
      · by_cases hb : p.val + 1 = n
        · right; left
          exact ⟨by omega, by omega, by omega⟩
        · left
          exact ⟨by omega, by omega, by omega, by omega⟩
      · right; right; right; right
        exact ⟨by omega, by omega, by rcases hq with h | h <;> omega⟩
  · intro h
    simp only [pell_nfa]
    rcases h with ⟨hk, hp1, hp2, hq⟩ | ⟨hk, hpn, hq⟩ | ⟨hk, hp3, hq⟩ | ⟨hk, hpn2, hq⟩ | ⟨hk, hp3', hq⟩
    · refine ⟨p.val, by omega, by omega, ?_⟩
      left
      refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
      rcases hq with h | h <;> omega
    · refine ⟨n - 2, by omega, by omega, ?_⟩
      right
      refine ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
    · refine ⟨p.val + 1, by omega, by omega, ?_⟩
      left
      refine ⟨by omega, Or.inl ⟨by omega, ?_⟩⟩
      rcases hq with h | h <;> omega
    · refine ⟨p.val, by omega, by omega, ?_⟩
      right
      refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    · refine ⟨p.val + 1, by omega, by omega, ?_⟩
      right
      refine ⟨by omega, Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
      rcases hq with h | h <;> omega
