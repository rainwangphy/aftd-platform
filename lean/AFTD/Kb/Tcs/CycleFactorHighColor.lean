import AFTD.Prelude

/-!
# cycle_factor_high_color

Topic: graphs   Node: fc2f1e564fb3

Provenance: helper lemma. Local cycle/chord ownership construction for the OP-874 campaign.

Embed the four factor-edge colors into the upper four of six colors.
-/

def cycle_factor_high_color (x : Fin 4) : Fin 6 := ⟨x.val + 2, by omega⟩
