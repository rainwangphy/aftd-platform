import AFTD.Prelude

/-!
# five_wheel_four

Topic: graphs   Node: c1cd8a35de04

Provenance: helper lemma. step towards degree_list_kempe_diameter_five

The 4-wheel W4: hub 0 joined to all of the rim, rim the 4-cycle 1-2-3-4; equivalently K5 minus the matching {{1,3},{2,4}}. Degrees (4,3,3,3,3), degree sum 16.
-/

/-- The wheel W₄ = K₅ minus the matching {{1,3},{2,4}} (one of the two 3-connected non-complete graphs on 5 vertices). Declared as an `abbrev` so that `DecidableRel five_wheel_four.Adj` is found by instance search. -/
abbrev five_wheel_four : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {Sym2.mk (1 : Fin 5) (3 : Fin 5), Sym2.mk (2 : Fin 5) (4 : Fin 5)}
