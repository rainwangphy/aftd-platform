import AFTD.Prelude

/-!
# procurement_others_bids

Topic: mechanism_design   Node: 83814dede794

The list of all bids of agents other than i in a profile where each agent submits a list of bids.
-/

def procurement_others_bids {n : ℕ} (β : Fin n → List ℝ) (i : Fin n) : List ℝ :=
  (List.finRange n).flatMap (fun j => if j = i then [] else β j)
