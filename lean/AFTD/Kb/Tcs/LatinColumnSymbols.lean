import AFTD.Prelude

/-!
# latin_column_symbols

Topic: combinatorics   Node: 26917ebe2c41

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The finite set of symbols appearing in column j of a fixed filling T of a Young diagram d.
-/

def latin_column_symbols (d : YoungDiagram) (T : d.cells → ℕ) (j : ℕ) : Finset ℕ :=
  (d.cells.attach.filter (fun c => c.val.2 = j)).image T
