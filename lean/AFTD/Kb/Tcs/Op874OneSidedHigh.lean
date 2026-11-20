import AFTD.Prelude

/-!
# op874_one_sided_high

Topic: graphs   Node: d116ac5adf09

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

Embed the four high colors as colors two through five.
-/

def op874_one_sided_high (c : Fin 4) : Fin 6 := ⟨c.val + 2, by have := c.isLt; omega⟩
