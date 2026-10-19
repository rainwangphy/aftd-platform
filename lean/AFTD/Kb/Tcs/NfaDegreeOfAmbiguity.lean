import AFTD.Prelude

/-!
# nfa_degree_of_ambiguity

Topic: automata   Node: a587d07cd3c8

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 1

The degree of ambiguity of an NFA M is the supremum in ℕ∞ over all words w of the number of accepting runs of M on w, measured by Set.encard.
-/

/-- The degree of ambiguity of an NFA is the supremum in ℕ∞ over all words of its number of accepting runs. -/
noncomputable def nfa_degree_of_ambiguity {α σ : Type*} (M : NFA α σ) : ℕ∞ :=
  ⨆ (w : List α),
    Set.encard { r : Fin (w.length + 1) → σ |
      r 0 ∈ M.start ∧
      r (Fin.last w.length) ∈ M.accept ∧
      ∀ (i : Fin w.length), r i.succ ∈ M.step (r i.castSucc) (w.get i) }
