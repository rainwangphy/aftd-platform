import AFTD.Prelude

/-!
# op874_ten_vertex_no_strict_cut_seven_matchings

Topic: graphs   Node: f57b98e04f5a

Provenance: helper lemma. Finite obstruction to a strict matching-cut shortcut for OP-874, experiments 43520 and 43523.

For the graph on vertices 0 through 9 with edges (0,1),(0,2),(0,4),(1,6),(1,8),(2,3),(2,4),(3,6),(3,8),(4,5),(5,7),(5,9),(6,7),(7,9),(8,9), and each of the seven listed pairings (01,23,45,67,89), (01,24,36,57,89), (01,24,38,59,67), (02,16,38,45,79), (02,18,36,45,79), (04,16,23,57,89), and (04,18,23,59,67), contract each listed pair. For every Boolean assignment to the five contracted pairs, some pair has at least two incident nonmatching edges whose other endpoint has the same Boolean value, counted with multiplicity. The seven pairings are indexed by the displayed partition table; their exhaustive classification as perfect matchings is a separate claim.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace IN1276

def left : Fin 15 → Fin 10 := ![0,0,0,1,1,2,2,3,3,4,5,5,6,7,8]
def right : Fin 15 → Fin 10 := ![1,2,4,6,8,3,4,6,8,5,7,9,7,9,9]
def part : Fin 7 → Fin 10 → Fin 5 :=
  ![![0,0,1,1,2,2,3,3,4,4],
    ![0,0,1,2,1,3,2,3,4,4],
    ![0,0,1,2,1,3,4,4,2,3],
    ![0,1,0,2,3,3,1,4,2,4],
    ![0,1,0,2,3,3,2,4,1,4],
    ![0,1,2,2,0,3,1,3,4,4],
    ![0,1,2,2,0,3,4,4,1,3]]

def sameDegree (i : Fin 7) (b : Fin 5 → Bool) (v : Fin 5) : Nat :=
  (Finset.univ.filter fun e : Fin 15 =>
    part i (left e) ≠ part i (right e) ∧
    (part i (left e) = v ∨ part i (right e) = v) ∧
    b (part i (left e)) = b (part i (right e))).card

theorem cut_kernel (i : Fin 7) (b0 b1 b2 b3 b4 : Bool) :
    ∃ v : Fin 5, 2 ≤ sameDegree i ![b0,b1,b2,b3,b4] v := by
  fin_cases i <;> revert b0 b1 b2 b3 b4 <;> decide

theorem all_cuts (i : Fin 7) (b : Fin 5 → Bool) :
    ∃ v : Fin 5, 2 ≤ sameDegree i b v := by
  have heq : ![b 0,b 1,b 2,b 3,b 4] = b := by
    funext v
    fin_cases v <;> rfl
  rw [← heq]
  exact cut_kernel i (b 0) (b 1) (b 2) (b 3) (b 4)

end IN1276

theorem op874_ten_vertex_no_strict_cut_seven_matchings :
  let L : Fin 15 → Fin 10 := ![0,0,0,1,1,2,2,3,3,4,5,5,6,7,8]
  let R : Fin 15 → Fin 10 := ![1,2,4,6,8,3,4,6,8,5,7,9,7,9,9]
  let part : Fin 7 → Fin 10 → Fin 5 := ![![0,0,1,1,2,2,3,3,4,4],![0,0,1,2,1,3,2,3,4,4],![0,0,1,2,1,3,4,4,2,3],![0,1,0,2,3,3,1,4,2,4],![0,1,0,2,3,3,2,4,1,4],![0,1,2,2,0,3,1,3,4,4],![0,1,2,2,0,3,4,4,1,3]]
  ∀ (i : Fin 7) (b : Fin 5 → Bool),
    ∃ v : Fin 5, 2 ≤ ((Finset.univ : Finset (Fin 15)).filter fun e =>
      part i (L e) ≠ part i (R e) ∧
      (part i (L e) = v ∨ part i (R e) = v) ∧
      b (part i (L e)) = b (part i (R e))).card := by
  dsimp only
  exact IN1276.all_cuts
