import AFTD.Prelude

/-!
# op874_four_square_open_port_cut_bound

Topic: graphs   Node: f8266b4bbb88

Provenance: helper lemma. OP-874; opened four-square obstruction block, experiment 41908.

After one matching edge in the four-square obstruction is opened into two independently assigned ports, any cut constant on the other seven matching edges crosses at most twelve of the sixteen factor edges. The displayed ordered list records every factor edge after the seven contractions; repeated pairs represent distinct original edges.
-/

theorem op874_four_square_open_port_cut_bound
    (a b c d e f g h i : Bool) :
    (([(e,f),(e,a),(f,e),(e,a),(g,c),(g,d),(c,g),(g,d),
       (d,c),(d,b),(c,h),(h,b),(i,b),(i,a),(b,f),(f,a)] : List (Bool × Bool)).filter
       (fun p => p.1 != p.2)).length ≤ 12 := by
  set_option maxHeartbeats 3000000 in
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    cases f <;> cases g <;> cases h <;> cases i <;> decide
