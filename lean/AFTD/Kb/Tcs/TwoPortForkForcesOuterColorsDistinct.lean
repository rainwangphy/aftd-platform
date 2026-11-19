import AFTD.Prelude

/-!
# two_port_fork_forces_outer_colors_distinct

Topic: combinatorics   Node: afd8d6349228

Provenance: helper lemma. Palette obstruction reduction for the OP-874 campaign.

A selected two-edge fork forces three outer-color inequalities from its local exposed-port constraints.
-/

theorem two_port_fork_forces_outer_colors_distinct
    {Ω : Type*} (a b c f x y : Ω)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : x = a ∨ x = f) (hy : y = b ∨ y = c) (hxy : x ≠ y) :
    f ≠ b ∧ a ≠ c ∧ f ≠ c := by
  have hxf : x = f := hx.resolve_left hxa
  have hyc : y = c := hy.resolve_left hyb
  subst x
  subst y
  exact ⟨hxb, Ne.symm hya, hxy⟩
