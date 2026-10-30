import AFTD.Prelude
import AFTD.Kb.Tcs.ThueMorseWord

/-!
# thue_morse_word_length

Topic: combinatorics   Node: 803c9a6a0ebf

Provenance: helper lemma. arXiv:2610.10950

For every natural number n, the length of the n-th Thue-Morse word t_n is 2^n.
-/

lemma thue_morse_word_length_aux {α β : Type*} (f : α → List β) (k : ℕ) (hk : ∀ b, (f b).length = k) (l : List α) :
    (l.flatMap f).length = k * l.length := by
  induction' l with b bs ih
  · rfl
  · rw [List.flatMap_cons, List.length_append, ih, hk, List.length_cons, mul_add, mul_one, add_comm]

/-- The length of the n-th Thue-Morse word is 2^n. -/
theorem thue_morse_word_length (n : ℕ) : (thue_morse_word n).length = 2^n := by
  induction' n with n ih
  · rfl
  · rw [thue_morse_word]
    rw [thue_morse_word_length_aux _ 2 (fun b => by cases b <;> rfl)]
    rw [ih, Nat.pow_succ, mul_comm]
