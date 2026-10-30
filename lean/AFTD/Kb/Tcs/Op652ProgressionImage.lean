import AFTD.Prelude

/-!
# op652_progression_image

Topic: graphs   Node: a89d4e0ff6f9

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The progression image {37 + 1·t : 0 ≤ t < 36} = {37, 38, …, 72}, as an explicit Finset ℤ.
-/

/-- The set {37,...,72} = image of 37+1·t for t < 36, the small carrier for the progression side of the model graph. -/
def op652_progression_image : Finset ℤ := (Finset.range 36).image (fun t : ℕ => 37 + 1 * (t : ℤ))
