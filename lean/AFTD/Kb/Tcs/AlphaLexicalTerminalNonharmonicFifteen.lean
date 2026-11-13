import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt

/-!
# alpha_lexical_terminal_nonharmonic_fifteen

Topic: combinatorics   Node: 15891f4b7aef

Provenance: helper lemma. Computed obstruction to a simplified periodicity route for OP-392, arXiv:2610.24758; lexical order, elementary operations and harmonics follow arXiv:0810.5205, Section 1.1 and Section 2.

The lexical sequence (2,1,2,2,1,1,1,2,1,1) has degree 14 and a lexical prefix of length two. Splitting the cell at index two is nonlexical, every later even-indexed elementary operation is also nonlexical, and the sequence is not the first harmonic u_o u of any sequence u.
-/

set_option maxHeartbeats 1000000

instance (a b : List ℕ) : Decidable (alpha_lexical_lt a b) := by
  unfold alpha_lexical_lt
  infer_instance
instance (a : List ℕ) : Decidable (alpha_is_lexical a) := by
  unfold alpha_is_lexical
  infer_instance

private def oddExt (u : List ℕ) : List ℕ :=
  if u.length % 2 = 0 then u ++ [1] else u.dropLast ++ [u.getLastD 0 + 1]
private def op (a : List ℕ) (i : ℕ) : List ℕ :=
  if 1 < a.getD i 0 then a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)
  else a.take (i-1) ++ [a.getD (i-1) 0 + 1] ++ a.drop (i + 1)
private def w : List ℕ := [2,1,2,2,1,1,1,2,1,1]

private theorem finiteFacts : alpha_is_lexical w ∧ w.sum + 1 = 15 ∧
    alpha_is_lexical (w.take 2) ∧ ¬ alpha_is_lexical (op w 2) ∧
    ∀ j : Fin 10, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op w j.val) := by decide

theorem alpha_lexical_terminal_nonharmonic_fifteen :
  let a : List ℕ := [2,1,2,2,1,1,1,2,1,1]
  alpha_is_lexical a ∧ a.sum + 1 = 15 ∧
  alpha_is_lexical (a.take 2) ∧
  ¬ alpha_is_lexical (a.take 2 ++ [a.getD 2 0 - 1, 1] ++ a.drop 3) ∧
  (∀ j : Fin 10, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical
    (if 1 < a.getD j.val 0 then
      a.take j.val ++ [a.getD j.val 0 - 1, 1] ++ a.drop (j.val + 1)
     else a.take (j.val - 1) ++ [a.getD (j.val - 1) 0 + 1] ++ a.drop (j.val + 1))) ∧
  ¬ ∃ u : List ℕ, a =
    (if u.length % 2 = 0 then u ++ [1] else u.dropLast ++ [u.getLastD 0 + 1]) ++ u := by
  change alpha_is_lexical w ∧ w.sum + 1 = 15 ∧
    alpha_is_lexical (w.take 2) ∧ ¬ alpha_is_lexical (op w 2) ∧
    (∀ j : Fin 10, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical (op w j.val)) ∧
    ¬ ∃ u : List ℕ, w = oddExt u ++ u
  refine ⟨finiteFacts.1, finiteFacts.2.1, finiteFacts.2.2.1,
    finiteFacts.2.2.2.1, finiteFacts.2.2.2.2, ?_⟩
  rintro ⟨u, hu⟩
  have hl := congrArg List.length hu
  have hlen : u.length = 5 := by
    simp only [w, List.length_cons, List.length_nil, List.length_append, oddExt] at hl
    split at hl <;> simp only [List.length_append, List.length_dropLast,
      List.length_cons, List.length_nil] at hl <;> omega
  have hext : (oddExt u).length = 5 := by
    simp [oddExt, hlen, List.length_dropLast]
  have hd : w.drop 5 = u := by
    rw [hu, ← hext]
    simp
  have heq : u = [1,1,2,1,1] := by
    simpa [w] using hd.symm
  rw [heq] at hu
  norm_num [w, oddExt] at hu
