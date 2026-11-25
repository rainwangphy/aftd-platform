import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexSet

/-!
# subtraction_grundy

Topic: combinatorial_games   Node: 4f418897bf76

Provenance: formalization of a published result. Source: arXiv:2611.30147, line 199 (equation 1)

The ordinary Sprague-Grundy sequence g_S : ℕ → ℕ of a subtraction game with move set S ⊆ ℕ is defined recursively by g_S(n) = mex {g_S(n - s) : s ∈ S, 0 < s ≤ n}.
-/

/-- Ordinary Sprague-Grundy sequence of a subtraction game with move set S. -/
noncomputable def subtraction_grundy (S : Set ℕ) : ℕ → ℕ :=
  WellFounded.fix (measure id).wf fun n ih =>
    nat_mex_set {k | ∃ s ∈ S, ∃ (hs : 0 < s) (hle : s ≤ n), k = ih (n - s) (Nat.sub_lt_self hs hle)}
