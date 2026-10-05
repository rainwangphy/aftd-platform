import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMTree

/-!
# pmAlg

Topic: algorithms   Node: 771b9b91b597

The candidate-list algorithm (Theorem 11 of arXiv 0707.1532, for width 2): scan the elements in order, keeping the (at most two) minimal elements of the prefix; a new element is compared with the candidates one by one. m is the number of elements still to scan.
-/

open Finset in
/-- The candidate-list algorithm (Theorem 11 of arXiv 0707.1532, for width 2): scan the elements in order, keeping the (at most two) minimal elements of the prefix; a new element is compared with the candidates one by one. `m` is the number of elements still to scan. -/
def pmAlg {n : ℕ} : ℕ → ℕ → List (Fin n) → PMTree n := fun
  | 0, _, cs => PMTree.leaf cs.toFinset
  | m + 1, k, cs =>
    if h : k < n then
      match cs with
      | [] => pmAlg m (k + 1) [⟨k, h⟩]
      | [t] => PMTree.node ⟨k, h⟩ t (fun r => match r with
          | PMAns.lt => pmAlg m (k + 1) [⟨k, h⟩]
          | PMAns.gt => pmAlg m (k + 1) [t]
          | PMAns.inc => pmAlg m (k + 1) [t, ⟨k, h⟩])
      | [t1, t2] => PMTree.node ⟨k, h⟩ t1 (fun r => match r with
          | PMAns.gt => pmAlg m (k + 1) [t1, t2]
          | PMAns.lt => PMTree.node ⟨k, h⟩ t2 (fun r2 => match r2 with
              | PMAns.lt => pmAlg m (k + 1) [⟨k, h⟩]
              | PMAns.gt => pmAlg m (k + 1) [t1, t2]
              | PMAns.inc => pmAlg m (k + 1) [t2, ⟨k, h⟩])
          | PMAns.inc => PMTree.node ⟨k, h⟩ t2 (fun r2 => match r2 with
              | PMAns.gt => pmAlg m (k + 1) [t1, t2]
              | PMAns.lt => pmAlg m (k + 1) [t1, ⟨k, h⟩]
              | PMAns.inc => pmAlg m (k + 1) [t1, t2]))
      | _ => PMTree.leaf ∅
    else PMTree.leaf cs.toFinset
