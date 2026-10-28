import AFTD.Prelude

/-!
# gen_k_server_uniform_path_cost

Topic: online_algorithms   Node: ca7cefa031b2

Provenance: formalization of a published result. Source: arXiv:2610.37192, Sec. 2: cost of an offline solution, sum of Hamming distances between consecutive configurations

For a start configuration x : Fin k → Fin m and a list of configurations, the path cost is defined by recursion on the list: 0 for the empty list, and for y :: ys it is hammingDist x y plus the path cost from y of ys. It is the total number of server moves along x, then the listed configurations in order.
-/

/-- Movement cost of visiting the listed configurations in order from `x` (unit distances). -/
def gen_k_server_uniform_path_cost {k m : ℕ} : (Fin k → Fin m) → List (Fin k → Fin m) → ℕ
  | _, [] => 0
  | x, y :: ys => hammingDist x y + gen_k_server_uniform_path_cost y ys
