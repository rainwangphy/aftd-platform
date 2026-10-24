import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape

/-!
# latin_double_three_tail_profile_last_column_card

Topic: combinatorics   Node: 29a35d024393

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

A profile has exactly one distinct symbol in its last column, as required by the one-cell last column of the shape.
-/

theorem latin_double_three_tail_profile_last_column_card (k : ℕ)
    (T : (latin_double_three_tail_shape k).cells → ℕ)
    (h : latin_double_three_tail_profile k T) :
    (latin_column_symbols (latin_double_three_tail_shape k) T (k - 1)).card = 1 := by
  obtain ⟨s, hs, c, hc, hfirst, hmid, hpair, hlast⟩ := h
  rw [hlast]
  simp
