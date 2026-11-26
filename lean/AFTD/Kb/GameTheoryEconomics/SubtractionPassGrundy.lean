import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SubtractionGrundy
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# subtraction_pass_grundy

Topic: combinatorial_games   Node: bd8ce9b41c42

Provenance: formalization of a published result. Source: arXiv:2611.30147, Section 2, Eq. (2)

The pass-available Sprague-Grundy sequence h_S : ℕ → ℕ of a subtraction game with move set S ⊆ ℕ is defined recursively by h_S(n) = mex ({h_S(n - s) : s ∈ S, 0 < s ≤ n} ∪ {g_S(n)}) when there is at least one legal move s ∈ S with 0 < s ≤ n, and h_S(n) = 0 otherwise.
-/

/-- The pass-available Sprague-Grundy sequence of a subtraction game with move set S. -/
noncomputable def subtraction_pass_grundy (S : Set ℕ) : ℕ → ℕ :=
  open Classical in
  WellFounded.fix (measure id).wf fun n ih =>
    if ∃ s ∈ S, 0 < s ∧ s ≤ n then
      nat_mex_set ({k | ∃ s ∈ S, ∃ (_hs : 0 < s) (_hle : s ≤ n), k = ih (n - s) (Nat.sub_lt_self _hs _hle)} ∪
        {subtraction_grundy S n})
    else 0
