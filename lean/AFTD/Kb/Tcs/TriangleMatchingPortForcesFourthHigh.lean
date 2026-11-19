import AFTD.Prelude

/-!
# triangle_matching_port_forces_fourth_high

Topic: combinatorics   Node: 98093637a296

Provenance: helper lemma. Palette obstruction reduction for the OP-874 campaign.

The triangle palette constraints force the same fourth high color at two outgoing ports.
-/

theorem triangle_matching_port_forces_fourth_high
    {Ω : Type*} (a b d x y u v z w t : Ω)
    (h5 : (x = b ∧ y = d) ∨ (x = d ∧ y = b))
    (h7 : (u = a ∧ v = d) ∨ (u = d ∧ v = a))
    (hxu : x ≠ u) (hxv : x ≠ v)
    (h6 : z = d ∨ w = d ∨ t = d)
    (hyw : y ≠ w) (hyt : y ≠ t) (hzv : z ≠ v) :
    y = d ∧ z = d ∧ u = d := by
  have hy : y = d := by
    rcases h5 with h | h
    · exact h.2
    · rcases h7 with h' | h'
      · exact False.elim (hxv (h.1.trans h'.2.symm))
      · exact False.elim (hxu (h.1.trans h'.1.symm))
  have hz : z = d := by
    rcases h6 with h | h | h
    · exact h
    · exact False.elim (hyw (hy.trans h.symm))
    · exact False.elim (hyt (hy.trans h.symm))
  have hu : u = d := by
    rcases h7 with h | h
    · exact False.elim (hzv (hz.trans h.2.symm))
    · exact h.1
  exact ⟨hy, hz, hu⟩
