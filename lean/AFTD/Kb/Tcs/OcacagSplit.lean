import AFTD.Prelude

/-!
# ocacagSplit

Topic: online_algorithms   Node: 1e6c9d6fb7af

Provenance: helper lemma. step towards online_cycle_augmentation_adversary_cost_ge

Bisect the integer interval c = [c.1, c.2] at its midpoint m = floor((c.1+c.2)/2), returning the half that contains v: [c.1, m] if v ≤ m, else [m+1, c.2].
-/

/-- One step of the dyadic bisection, keeping the half that contains `v`. -/
def ocacagSplit (c : ℤ × ℤ) (v : ℤ) : ℤ × ℤ := if v ≤ (c.1 + c.2) / 2 then (c.1, (c.1 + c.2) / 2) else ((c.1 + c.2) / 2 + 1, c.2)
