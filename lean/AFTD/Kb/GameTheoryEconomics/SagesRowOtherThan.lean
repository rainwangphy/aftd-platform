import AFTD.Prelude

/-!
# sages_row_other_than

Topic: combinatorial_games   Node: ffaee15ef066

Provenance: helper lemma. step towards sages_row_upper_bound_binomial

For S ≥ 2 sages, a canonical sage other than a given sage x: seat 1 if x occupies seat 0, and seat 0 otherwise.
-/

/-- A default partner distinct from x, used by `sages_row_pair_protocol` on local views that carry no neighbour at all. -/
def sages_row_other_than {S : ℕ} (hS : 2 ≤ S) (x : Fin S) : Fin S := ⟨if x.val = 0 then 1 else 0, by split_ifs with h <;> omega⟩
