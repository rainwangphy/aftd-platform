import AFTD.Prelude

/-!
# ternary_nae

Topic: quantum   Node: 7fe483f31650

Provenance: formalization of a published result. Source: arXiv:2611.16412 Section 5

The ternary not-all-equal Boolean function NAE₃ on 3 bits, which outputs 0 on 000 and 111 and 1 otherwise.
-/

/-- The ternary not-all-equal Boolean function on 3 bits, outputting 0 on 000 and 111 and 1 otherwise. -/
def ternary_nae (x : Fin 3 → Bool) : Bool := !((x 0 == x 1) && (x 1 == x 2))
