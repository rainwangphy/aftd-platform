import AFTD.Prelude

/-!
# cycle_with_two_chords

Topic: graphs   Node: fa1ba03b77f6

Provenance: formalization of a published result. Source: arXiv:2610.17884 Lemma 4.1

The simple graph on vertices 0, ..., m - 1 obtained from the cycle graph on m vertices by adding two chords: one between vertex 0 and vertex a - 1, and one between vertex a and vertex m - 1 (corresponding to chords {1, a} and {a+1, m} in 1-based indexing).
-/

/-- The m-cycle with two chords {1, a} and {a+1, m} in 1-based indexing. -/
def cycle_with_two_chords (m a : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.cycleGraph m ⊔ SimpleGraph.fromRel fun u v =>
    (u.val = 0 ∧ v.val = a - 1) ∨ (u.val = a ∧ v.val = m - 1)
