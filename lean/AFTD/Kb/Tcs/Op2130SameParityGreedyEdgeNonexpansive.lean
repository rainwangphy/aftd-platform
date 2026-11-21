import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_2130_same_parity_greedy_edge_nonexpansive

Topic: online_algorithms   Node: 816e69f4fb69

Provenance: helper lemma. OP-2130: synchronized greedy coupling as a route to pathwise concentration

Apply the same greedy edge update and tie coin to two integer endpoint pairs. If corresponding endpoint values have the same parity, the sum of squared differences of the pairs cannot increase.
-/

theorem op_2130_same_parity_greedy_edge_nonexpansive (x y z w : ℤ) (c : Bool) (hx : Even (x - z)) (hy : Even (y - w)) : let a : ℤ := if x < y then 1 else if y < x then -1 else if c then 1 else -1; let b : ℤ := if z < w then 1 else if w < z then -1 else if c then 1 else -1; (x + a - (z + b))^2 + (y - a - (w - b))^2 ≤ (x - z)^2 + (y - w)^2 := by
  rcases hx with ⟨p, hp⟩
  rcases hy with ⟨q, hq⟩
  have hsep : x - y = z - w ∨ x - y + 2 ≤ z - w ∨ z - w + 2 ≤ x - y := by omega
  rcases hsep with heq | hle | hge <;> cases c <;> dsimp <;> split_ifs <;> nlinarith
