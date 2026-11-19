import AFTD.Prelude

/-!
# cycle_matching_low_color

Topic: graphs   Node: c7dc4730eb8a

Provenance: helper lemma. Local cycle/chord ownership construction for the OP-874 campaign.

The low external matching color associated with a bit.
-/

def cycle_matching_low_color (b : Bool) : Fin 6 := if b then 1 else 0
