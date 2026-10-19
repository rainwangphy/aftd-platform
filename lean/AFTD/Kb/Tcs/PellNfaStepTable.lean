import AFTD.Prelude
import AFTD.Kb.Tcs.PellNfa

/-!
# pell_nfa_step_table

Topic: automata   Node: f408ff636a06

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

In A_n, if q is reachable from p in one step on letter k, then one of the following holds: (i) k ≡ p (mod 5) and q = p or q = p+1; (ii) k ≡ p+1 (mod 5) and q = p or q = p+2; (iii) k ≡ p+2 (mod 5) and q = p+1 or q = p+2. In particular all transitions are nondecreasing in the state index and jump by at most 2, and the letters of residues k ≡ p+3, p+4 (mod 5) are dead at p.
-/

/-- Local transition table of `pell_nfa n`: from state ⟨p⟩ only the three letters of residue p, p+1, p+2 (mod 5) are readable, and they act by staying or by jumping one/two places. -/
theorem pell_nfa_step_table (n : ℕ) {p q : Fin n} {k : Fin 5}
    (h : q ∈ (pell_nfa n).step p k) :
    (k.val = p.val % 5 ∧ (q.val = p.val ∨ q.val = p.val + 1)) ∨
    (k.val = (p.val + 1) % 5 ∧ (q.val = p.val ∨ q.val = p.val + 2)) ∨
    (k.val = (p.val + 2) % 5 ∧ (q.val = p.val + 1 ∨ q.val = p.val + 2)) := by
  simp only [pell_nfa] at h
  obtain ⟨i, hi1, hi2, h⟩ := h
  rcases h with h | h
  · obtain ⟨hk, hpq⟩ := h
    rcases hpq with ⟨hp1, hq⟩ | ⟨hp2, hq⟩
    · right; left
      exact ⟨by omega, by rcases hq with hq | hq <;> omega⟩
    · left
      exact ⟨by omega, by rcases hq with hq | hq <;> omega⟩
  · obtain ⟨hk, hpq⟩ := h
    rcases hpq with ⟨hp1, hq1⟩ | ⟨hp2, hq2⟩ | ⟨hp3, hq⟩
    · right; left
      exact ⟨by omega, by omega⟩
    · left
      exact ⟨by omega, by omega⟩
    · right; right
      exact ⟨by omega, by rcases hq with hq | hq <;> omega⟩
