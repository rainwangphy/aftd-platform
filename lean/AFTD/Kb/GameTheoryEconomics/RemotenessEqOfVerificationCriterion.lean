import AFTD.Prelude

/-!
# remoteness_eq_of_verification_criterion

Topic: combinatorial_games   Node: 6a33f1d05783

Provenance: formalization of a published result. Source: arXiv:2611.27343 (A general reduction and explicit remoteness formulas for exact slow 2-Nim), Lemma 2.1 (verification criterion); remoteness is taken as any function satisfying the recursion (2.1), which determines it uniquely on a well-founded game.

Consider an impartial game whose positions form a type V, each position x having a finite set of options opt x, such that every sequence of moves terminates (the option relation is well-founded); a position is terminal when it has no options. Let R : V → ℕ be the remoteness function, given by the recursion: R(x) = 0 at terminal x; if some option y of x has R(y) even, then R(x) = 1 + the minimum of R(y) over options with R(y) even; otherwise (x nonterminal, no even option) R(x) = 1 + the maximum of R(y) over all options. Let F : V → ℕ vanish at terminal positions and satisfy, at every nonterminal x: (1) if F(x) is even, every option y has F(y) odd and F(y) ≤ F(x) − 1, and some option has F(y) = F(x) − 1; (2) if F(x) is odd, some option has F(y) = F(x) − 1, and every option y with F(y) even has F(y) ≥ F(x) − 1. Then F = R. (Here F(y) ≤ F(x) − 1 and F(y) = F(x) − 1 are read in the integers, as F(y) + 1 ≤ F(x) and F(y) + 1 = F(x); minimum and maximum are expressed as attained bounds.)
-/

theorem remoteness_eq_of_verification_criterion {V : Type*} (opt : V → Finset V)
    (hwf : WellFounded fun y x => y ∈ opt x) (R F : V → ℕ)
    (hR0 : ∀ x, opt x = ∅ → R x = 0)
    (hReven : ∀ x, (∃ y ∈ opt x, Even (R y)) →
      (∃ y ∈ opt x, Even (R y) ∧ R x = R y + 1) ∧
        ∀ y ∈ opt x, Even (R y) → R x ≤ R y + 1)
    (hRodd : ∀ x, opt x ≠ ∅ → (∀ y ∈ opt x, ¬ Even (R y)) →
      (∃ y ∈ opt x, R x = R y + 1) ∧ ∀ y ∈ opt x, R y + 1 ≤ R x)
    (hF0 : ∀ x, opt x = ∅ → F x = 0)
    (hFeven : ∀ x, opt x ≠ ∅ → Even (F x) →
      (∀ y ∈ opt x, Odd (F y) ∧ F y + 1 ≤ F x) ∧ ∃ y ∈ opt x, F y + 1 = F x)
    (hFodd : ∀ x, opt x ≠ ∅ → Odd (F x) →
      (∃ y ∈ opt x, F y + 1 = F x) ∧ ∀ y ∈ opt x, Even (F y) → F x ≤ F y + 1) :
    F = R := by
  funext x
  induction x using hwf.induction with
  | _ x ih =>
    by_cases hx : opt x = ∅
    · rw [hF0 x hx, hR0 x hx]
    rcases Nat.even_or_odd (F x) with he | ho
    · obtain ⟨hall, y', hy', hy'F⟩ := hFeven x hx he
      have hnoeven : ∀ y ∈ opt x, ¬ Even (R y) := by
        intro y hy hev
        rw [← ih y hy] at hev
        exact Nat.not_even_iff_odd.2 (hall y hy).1 hev
      obtain ⟨⟨y, hy, hRy⟩, hRall⟩ := hRodd x hx hnoeven
      have h1 := (hall y hy).2
      have h2 := hRall y' hy'
      rw [← ih y hy] at hRy
      rw [← ih y' hy'] at h2
      omega
    · obtain ⟨⟨y, hy, hyF⟩, hFall⟩ := hFodd x hx ho
      have hyev : Even (F y) := by
        rcases Nat.even_or_odd (F y) with h | h
        · exact h
        · exfalso
          rw [← hyF] at ho
          exact Nat.not_even_iff_odd.2 ho (h.add_one)
      have hRyev : Even (R y) := by rw [← ih y hy]; exact hyev
      obtain ⟨⟨y1, hy1, hy1ev, hRx⟩, hRall⟩ := hReven x ⟨y, hy, hRyev⟩
      have h1 := hRall y hy hRyev
      have h2 := hFall y1 hy1 (by rw [ih y1 hy1]; exact hy1ev)
      rw [← ih y hy] at h1
      rw [ih y1 hy1] at h2
      omega
