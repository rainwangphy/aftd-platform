import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTopRowAvailability
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.MemLatinColumnSymbols

/-!
# latin_top_row_availability_eq_one_iff

Topic: combinatorics   Node: f6c440fbc2d7

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The availability entry equals one exactly when the prospective positive symbol does not already occur in that column.
-/

theorem latin_top_row_availability_eq_one_iff (d : YoungDiagram) (T : d.cells → ℕ)
    (w : ℕ) (i j : Fin w) :
    latin_top_row_availability d T w i j = 1 ↔
      i.val + 1 ∉ latin_column_symbols d T j.val := by
  simp [latin_top_row_availability, mem_latin_column_symbols]
