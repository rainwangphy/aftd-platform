import AFTD.Prelude

/-!
# latin_top_row_availability

Topic: combinatorics   Node: 79a09c8cbf7d

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The zero-one matrix whose row index is a prospective symbol minus one and whose column index is a column: an entry is one precisely when inserting that symbol above T creates no column conflict.
-/

def latin_top_row_availability (d : YoungDiagram) (T : d.cells → ℕ) (w : ℕ) :
    Matrix (Fin w) (Fin w) ℕ := fun i j =>
  if ∀ c : d.cells, c.val.2 = j.val → T c ≠ i.val + 1 then 1 else 0
