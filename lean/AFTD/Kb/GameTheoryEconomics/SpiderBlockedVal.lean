import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd

/-!
# spider_blocked_val

Topic: combinatorial_games   Node: ec78da2f4cbc

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

The conjectured closed form of the blocked two-leg family at incoming centre: for end condition inward it is m - 1 when m % 4 = 3 and m + 1 otherwise; for any other end condition (outward, and by convention free) it is m - 1 when m % 4 = 1 and m + 1 otherwise.
-/

/-- Closed form of the blocked 2-leg family (in;{(m,δ),(1,free)}): m-1 in the residue class 3 (mod 4) for δ = inward, 1 (mod 4) otherwise, and m+1 elsewhere. -/
def spider_blocked_val : SpiderLegEnd → ℕ → ℕ := fun δ m =>
  match δ with
  | SpiderLegEnd.inward => if m % 4 = 3 then m - 1 else m + 1
  | _ => if m % 4 = 1 then m - 1 else m + 1
