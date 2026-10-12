import AFTD.Prelude
import AFTD.Kb.Tcs.RegularExpressionTypedParity

/-!
# regular_expression_typed_parity_length

Topic: automata   Node: 839afcfe4b68

Provenance: helper lemma. Sanity lemma for regular_expression_typed_parity: the "immediate induction" remark after the typing rules in arXiv:2610.11717 (Every Regular Language Has a Bipartite Cactus Automaton), Sec. 3.1.

Every word in the language of an expression typed with parity p has length ≡ p (mod 2).
-/

theorem regular_expression_typed_parity_length {α : Type*} (r : RegularExpression α) (p : ZMod 2)
    (hr : regular_expression_typed_parity r p) (w : List α) (hw : w ∈ r.matches') :
    (w.length : ZMod 2) = p := by
  induction r generalizing p w with
  | zero =>
    change w ∈ (0 : Language α) at hw
    exact absurd hw (Language.notMem_zero w)
  | epsilon =>
    change w ∈ (1 : Language α) at hw
    rw [Language.mem_one] at hw
    subst hw
    simpa [regular_expression_typed_parity] using hr.symm
  | char a =>
    replace hw : w = [a] := hw
    subst hw
    simpa [regular_expression_typed_parity] using hr.symm
  | plus r s ihr ihs =>
    change w ∈ r.matches' + s.matches' at hw
    rw [Language.mem_add] at hw
    rcases hw with hw | hw
    · exact ihr p hr.1 w hw
    · exact ihs p hr.2 w hw
  | comp r s ihr ihs =>
    change w ∈ r.matches' * s.matches' at hw
    rw [Language.mem_mul] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    obtain ⟨q₁, q₂, hq, h₁, h₂⟩ := hr
    rw [List.length_append, Nat.cast_add, ihr q₁ h₁ a ha, ihs q₂ h₂ b hb, hq]
  | star r ihr =>
    change w ∈ KStar.kstar r.matches' at hw
    rw [Language.mem_kstar] at hw
    obtain ⟨L, rfl, hL⟩ := hw
    rw [hr.1]
    induction L with
    | nil => simp
    | cons y L ih =>
      rw [List.flatten_cons, List.length_append, Nat.cast_add,
        ihr 0 hr.2 y (hL y (List.mem_cons_self ..)),
        ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)), add_zero]
