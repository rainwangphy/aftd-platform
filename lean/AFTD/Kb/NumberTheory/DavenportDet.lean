import AFTD.Prelude

/-!
# davenport_det

Topic: elementary_number_theory   Node: 5d02e9f69c48

Provenance: helper lemma. step towards davenport_box_minimal_zero_sum_card_le_of_support_three

The signed area determinant det(p,q) = p.x*q.y - p.y*q.x of two points of the integer plane.
-/

/-- The 2x2 determinant det(p,q) = p.x*q.y - p.y*q.x of two plane integer points. -/
def davenport_det (p q : ℤ × ℤ) : ℤ := p.1 * q.2 - p.2 * q.1
