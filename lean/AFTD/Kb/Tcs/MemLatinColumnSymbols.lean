import AFTD.Prelude
import AFTD.Kb.Tcs.LatinColumnSymbols

/-!
# mem_latin_column_symbols

Topic: combinatorics   Node: 82692ec1845b

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

A symbol belongs to a column-symbol set exactly when a cell of that column has that value.
-/

theorem mem_latin_column_symbols (d : YoungDiagram) (T : d.cells → ℕ) (j x : ℕ) :
    x ∈ latin_column_symbols d T j ↔ ∃ c : d.cells, c.val.2 = j ∧ T c = x := by
  simp [latin_column_symbols]
