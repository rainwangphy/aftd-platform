import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_sum_pos

Topic: combinatorial_games   Node: b26d022b7516

Provenance: helper lemma. step towards arrows_twin_branch_reduction

The disjoint-sum position of a position p on G and a position q on H: the arrows of p are placed on the left copy, the arrows of q on the right copy, and no arrow crosses.
-/

/-- The pair of positions p and q viewed as a position on the disjoint sum graph. -/
def arrows_sum_pos {V W : Type*} (p : ArrowsPos V) (q : ArrowsPos W) : ArrowsPos (V ⊕ W) := ⟨fun x y => Sum.elim (fun a => Sum.elim (fun b => p.1 a b) (fun _ => false) y)
      (fun a => Sum.elim (fun _ => false) (fun b => q.1 a b) y) x, by
  rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true] at h ⊢
  · simpa using p.2 a b h
  · simpa using q.2 a b h⟩
