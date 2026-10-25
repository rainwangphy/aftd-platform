import AFTD.Prelude
import AFTD.Kb.Tcs.IsPermCover

/-!
# not_is_perm_cover_empty

Topic: automata   Node: b03ccbde21ea

Provenance: helper lemma. folklore, sanity lemma for is_perm_cover

For any natural number k, the empty set does not satisfy is_perm_cover k ∅.
-/

/-- The empty set is never a cover for the symmetric group on k elements. -/
theorem not_is_perm_cover_empty (k : ℕ) : ¬ is_perm_cover k ∅ := by
  intro h
  obtain ⟨d, hd, -⟩ := h.2 1
  exact Finset.notMem_empty d hd
