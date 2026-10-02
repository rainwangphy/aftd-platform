import AFTD.Prelude

/-!
# catch_up_search

Topic: combinatorial_games   Node: cede2cfb17cc

Pruned search over the Catch-Up game tree. With the last flag true it decides whether the player to move can force a win, with it false whether they can avoid losing; at their own moves it stops at the first good move.
-/

/-- Pruned search: `true` asks whether the mover can force a win, `false` whether they can avoid losing. -/
def catch_up_search : ℕ → List ℕ → ℕ → ℕ → Bool → Bool → Bool := fun
  | 0, _, s_me, s_opp, _, w => if w then decide (s_opp < s_me) else decide (s_opp ≤ s_me)
  | n + 1, l, s_me, s_opp, first, w =>
      match l with
      | [] => if w then decide (s_opp < s_me) else decide (s_opp ≤ s_me)
      | _ :: _ =>
        if s_me + l.sum < s_opp then false
        else l.any fun x =>
          if first || decide (s_opp ≤ s_me + x) then
            !(catch_up_search n (l.erase x) s_opp (s_me + x) false (!w))
          else catch_up_search n (l.erase x) (s_me + x) s_opp false w
