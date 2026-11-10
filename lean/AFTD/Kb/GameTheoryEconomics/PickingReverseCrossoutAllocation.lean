import AFTD.Prelude

/-!
# picking_reverse_crossout_allocation

Topic: fair_division   Node: 223c7d6a17f7

Provenance: helper lemma. Reverse crossout representation of two-agent sequential picking; see https://cdn.aaai.org/ojs/8697/8697-13-12225-1-2-20201228.pdf Theorem 1.

The allocation produced by a prescribed reverse picking order and a list of distinct selected goods: an agent receives exactly the selected goods at her turns in the reversed order.
-/

noncomputable def picking_reverse_crossout_allocation {n : ℕ}
    (s : List (Fin 2)) (π : Fin n → Fin n) (i : Fin 2) : Finset (Fin n) := (Finset.univ.filter fun t : Fin n => s.reverse.getD t.val 0 = i).image π
