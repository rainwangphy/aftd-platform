import AFTD.Prelude

/-!
# picking_reverse_crossout_valid

Topic: fair_division   Node: 50a12a386460

Provenance: helper lemma. Reverse crossout representation of two-agent sequential picking; see https://cdn.aaai.org/ojs/8697/8697-13-12225-1-2-20201228.pdf Theorem 1.

A reverse crossout sequence visits every item once and, at every reversed turn, selects an available item of minimum value for the other agent. The original picking order has exactly one turn per item.
-/

noncomputable def picking_reverse_crossout_valid {n : ℕ}
    (u : Fin 2 → Fin n → ℝ) (s : List (Fin 2)) (π : Fin n → Fin n) : Prop := s.length = n ∧ Function.Bijective π ∧
    ∀ t j : Fin n, t < j →
      u (if s.reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if s.reverse.getD t.val 0 = 0 then 1 else 0) (π j)
