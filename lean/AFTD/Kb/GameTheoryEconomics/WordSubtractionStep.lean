import AFTD.Prelude

/-!
# word_subtraction_step

Topic: combinatorial_games   Node: 390f088c6da7

Provenance: helper lemma. step towards word_subtraction_is_regular

The transition: push the new letter c onto the front of the buffer (shifting the rest right by one, dropping the oldest letter), shift the status bits up by one, and compute the new bit 0 as true iff some s in S is a suffix of the new word (read from the buffer) whose corresponding old prefix-status bit is false.
-/

/-- Transition function of the Theorem 2.9 automaton on state (buffer, status bits). -/
noncomputable def word_subtraction_step {α : Type*} (S : Finset (List α)) (n : ℕ) (hn : ∀ s ∈ S, s.length ≤ n) :
    (Fin n → Option α) × (Fin (n + 1) → Bool) → α → (Fin n → Option α) × (Fin (n + 1) → Bool) := fun st c =>
    let buf : Fin n → Option α :=
      fun i => if (i : ℕ) = 0 then some c else st.1 ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩
    let b0 : Bool := by
      classical
      exact decide (∃ s, ∃ hs : s ∈ S,
        (∀ i : Fin s.length,
          buf ⟨(i : ℕ), by have := i.isLt; have := hn s hs; omega⟩ = s.reverse[(i : ℕ)]?)
        ∧ st.2 ⟨s.length - 1, by have := hn s hs; omega⟩ = false)
    (buf, fun j => if (j : ℕ) = 0 then b0 else st.2 ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
