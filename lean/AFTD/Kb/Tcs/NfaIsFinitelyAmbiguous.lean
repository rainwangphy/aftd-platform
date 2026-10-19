import AFTD.Prelude

/-!
# nfa_is_finitely_ambiguous

Topic: automata   Node: 889af06ff5bf

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 2

An NFA M is finitely ambiguous if there exists a natural number N such that for every word w, the number of accepting runs Set.encard of M on w is at most N.
-/

/-- An NFA is finitely ambiguous if the number of accepting runs on any word is uniformly bounded. -/
def nfa_is_finitely_ambiguous {α σ : Type*} (M : NFA α σ) : Prop :=
  ∃ (N : ℕ), ∀ (w : List α),
    Set.encard { r : Fin (w.length + 1) → σ |
      r 0 ∈ M.start ∧
      r (Fin.last w.length) ∈ M.accept ∧
      ∀ (i : Fin w.length), r i.succ ∈ M.step (r i.castSucc) (w.get i) } ≤ N
