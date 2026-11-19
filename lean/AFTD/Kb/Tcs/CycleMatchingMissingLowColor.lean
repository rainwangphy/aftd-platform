import AFTD.Prelude

/-!
# cycle_matching_missing_low_color

Topic: graphs   Node: 5c76b98d8cab

Provenance: helper lemma. Local cycle/chord ownership construction for the OP-874 campaign.

The low color omitted from the external matching edge.
-/

def cycle_matching_missing_low_color (b : Bool) : Fin 6 := if b then 0 else 1
